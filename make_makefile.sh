#!/bin/sh

coq_makefile -R "." CoqBookPL -o makefile book/*v todo/*v todo/*/*v
