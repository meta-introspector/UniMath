#!/bin/bash
file_name=trace_log.txt
current_time=$(date "+%Y.%m.%d-%H.%M.%S")
new_fileName=$file_name.$current_time
echo building $new_fileName
make > $new_fileName  2>&1
tail $new_fileName  | grep Error: -B1
