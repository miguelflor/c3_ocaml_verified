#!/bin/bash
# filepath: /home/miguel/Desktop/ADC/adc_2025_c3/wikipedia_example/build.sh

ocamlc -o wikipedia_example types.ml c3.ml wikipedia_example.ml
./wikipedia_example