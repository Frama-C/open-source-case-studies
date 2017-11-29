#!/bin/sh -eu

if [ $# -lt 2 ]; then
    echo "usage: $0 dir target1 [target2 ...]"
    exit 1
fi

dir="$1"
shift

for target in "$@"; do
    secs=$(grep '^user_time=' $target/stats.txt | cut -d= -f2-)
    maxmem=$(grep '^memory=' $target/stats.txt | cut -d= -f2-)
    printf "$dir/$target: user time %.2fs, memory %d KiB\n" $secs $maxmem
done
