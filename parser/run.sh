#!/bin/sh

stack build && stack exec -- parser-exe $@
