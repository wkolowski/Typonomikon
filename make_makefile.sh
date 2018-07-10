#!/bin/sh

coq_makefile -R "." CoqBookPL -o makefile book/*v wd/*v
