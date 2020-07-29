#!/bin/bash

cd agda

agda --html --html-dir=../html SyntheticReals.agda
# agda --html --html-dir=../html MoreLogic.agda 

exit 0

cd ..
cd test

while read f; do
  agda --html --html-dir=../html "$f" 
done <(ls -1 *.agda)
