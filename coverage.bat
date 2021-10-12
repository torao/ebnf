@echo off
docker run --rm --security-opt seccomp=unconfined -v "%cd%:/volume" xd009642/tarpaulin sh -c "cargo tarpaulin -o Html"
