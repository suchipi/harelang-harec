#include <stdint.h>
#include <stdio.h>
#include "utf8.h"

static const struct {
	uint8_t mask;
	uint8_t result;
	int octets;
} sizes[] = {
	{ 0x80, 0x00, 1 },
	{ 0xE0, 0xC0, 2 },
	{ 0xF0, 0xE0, 3 },
	{ 0xF8, 0xF0, 4 },
};

static int
utf8_size(uint8_t c)
{
	for (size_t i = 0; i < sizeof(sizes) / sizeof(sizes[0]); ++i) {
		if ((c & sizes[i].mask) == sizes[i].result) {
			return sizes[i].octets;
		}
	}
	return -1;
}

size_t
utf8_encode(char *str, uint32_t ch)
{
	size_t len = 0;
	uint8_t first;

	if (ch < 0x80) {
		first = 0;
		len = 1;
	} else if (ch < 0x800) {
		first = 0xc0;
		len = 2;
	} else if (ch < 0x10000) {
		first = 0xe0;
		len = 3;
	} else {
		first = 0xf0;
		len = 4;
	}

	for (size_t i = len - 1; i > 0; --i) {
		str[i] = (ch & 0x3f) | 0x80;
		ch >>= 6;
	}

	str[0] = ch | first;
	return len;
}

uint32_t
utf8_get(FILE *f)
{
	char buffer[UTF8_MAX_SIZE];
	int c = fgetc(f);
	if (c == EOF) {
		return UTF8_INVALID;
	}
	buffer[0] = (char)c;
	int size = utf8_size(c);

	if (size > UTF8_MAX_SIZE) {
		fseek(f, size - 1, SEEK_CUR);
		return UTF8_INVALID;
	}

	if (size > 1) {
		int amt = fread(&buffer[1], 1, size - 1, f);
		if (amt != size - 1) {
			return UTF8_INVALID;
		}
	}
	const char *ptr = buffer;
	return utf8_decode(&ptr);
}

// UTF-8 decoder:
// Copyright (c) 2008-2009 Bjoern Hoehrmann <bjoern@hoehrmann.de>
// See http://bjoern.hoehrmann.de/utf-8/decoder/dfa/ for details.
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to
// deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
// IN THE SOFTWARE.

#define UTF8_ACCEPT 0
#define UTF8_REJECT 1

static const uint8_t utf8d[] = {
	0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,//00..1f
	0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,//20..3f
	0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,//40..5f
	0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,//60..7f
	1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,//80..9f
	7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,//a0..bf
	8,8,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,//c0..df
	0xa,0x3,0x3,0x3,0x3,0x3,0x3,0x3,0x3,0x3,0x3,0x3,0x3,0x4,0x3,0x3,//e0..ef
	0xb,0x6,0x6,0x6,0x5,0x8,0x8,0x8,0x8,0x8,0x8,0x8,0x8,0x8,0x8,0x8,//f0..ff
	0x0,0x1,0x2,0x3,0x5,0x8,0x7,0x1,0x1,0x1,0x4,0x6,0x1,0x1,0x1,0x1,//s0..s0
	1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,1,1,1,1,1,//s1..s2
	1,2,1,1,1,1,1,2,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,//s3..s4
	1,2,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,3,1,3,1,1,1,1,1,1,//s5..s6
	1,3,1,1,1,1,1,3,1,3,1,1,1,1,1,1,1,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,//s7..s8
};

uint32_t
utf8_decode(const char **char_str)
{
	const uint8_t **s = (const uint8_t **)char_str;
	uint32_t state = 0;
	uint32_t cp = 0;

	// Assumes char_str does not end with a partial code sequence.
	while (1) {
		uint8_t byte = **s;
		(*s)++;
		uint32_t type = utf8d[byte];
		cp = (state != UTF8_ACCEPT) ?
			(byte & 0x3fu) | (cp << 6) :
			(0xff >> type) & (byte);
		state = utf8d[256 + state * 16 + type];
		if (state == UTF8_REJECT) {
			return UTF8_INVALID;
		} else if (state == UTF8_ACCEPT) {
			return cp;
		}
	}
}
