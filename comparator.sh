export PATH=$PATH:/home/wwylele/lean4export/.lake/build/bin

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" --working-directory $(pwd) -- bash -c 'lake env ~/comparator/.lake/build/bin/comparator comparator.json'