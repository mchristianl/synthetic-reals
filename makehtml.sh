#!/bin/bash -x

# see https://jesper.sikanda.be/posts/literate-agda.html
# see https://agda.readthedocs.io/en/latest/tools/literate-programming.html
# see https://docs.github.com/en/github/working-with-github-pages/creating-a-github-pages-site
#   uses gh-pages branch
# see https://raw.githubusercontent.com/sindresorhus/github-markdown-css/gh-pages/github-markdown.css

cd agda

agda --html --html-highlight=auto --html-dir=../html HTML.lagda.md
# agda --html --html-dir=../html SyntheticReals.agda
# agda --html --html-dir=../html MoreLogic.agda 

cd ..

cd html

pandoc --metadata title="synthetic reals" -t html5 --standalone --katex -c Agda.css -c github-markdown.css HTML.md -o index.html

cd ..

exit 0

cd test

while read f; do
  agda --html --html-dir=../html "$f" 
done <(ls -1 *.agda)
