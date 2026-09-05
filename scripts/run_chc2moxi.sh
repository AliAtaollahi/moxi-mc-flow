#!/usr/bin/env bash

pushd $(dirname "$0")/../test/

echo "-----------------------------------------------------"
echo "Testing chc2moxi"
echo "-----------------------------------------------------"
python3 test.py chc2moxi.json

popd
