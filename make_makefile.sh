#!/bin/sh

coq_makefile -R "." CoqBookPL -o makefile book/*v wd2/*v #*v */*v */*/*v
