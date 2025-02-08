#!/bin/sh
rev=$(git log --format=format:%h HEAD^! || echo unknown)
year=$(date "+%Y")
echo "let version=\"revision ${rev}\"" > version.ml
echo "let copyright=\"Copyright 2010-${year} Codinuum Software Lab <codinuum@me.com>\"" >> version.ml
