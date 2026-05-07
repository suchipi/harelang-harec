#!/usr/bin/env bash

set -e

# cd harec
sudo cp rt/+darwin/build.sh /usr/local/bin/hare-build.sh
for f in arch qbe as ld cc; do
    sudo ln -sf ./hare-build.sh /usr/local/bin/hare-$f.sh
done
ln -sf configs/darwin.mk config.mk
make -j2
make check
#sudo -E make install
