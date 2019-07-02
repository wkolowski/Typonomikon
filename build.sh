#!/bin/sh

# Skompiluj pliki .v - dzięki temu mamy pewność, że cały kod z książki działa poprawnie.
make

./buildhtml.sh
./buildpdf.sh
