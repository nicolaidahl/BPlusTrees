#!/usr/bin/env python

import os
from pprint import pprint


class Lemma:
    def __init__(self, name, length):
        self.name = name
        self.length = length
        self.dependencies = []

    def __repr__(self):
        return self.name + ": " + str(self.length)

files = [f for f in os.listdir('.') if os.path.isfile(f) and f.endswith('.v')]

lemmas = set()

for fileName in files:
    print 'Looking in file:', fileName
    f = open(fileName, 'r')

    ln = 0
    lemma = ''

    for line in f:
        if line.startswith('Theorem') or line.startswith('Lemma'):
            lemmaName = line.split(' ')[1].split(':')[0]
            lemma = Lemma(lemmaName, ln)
            lemmas.add(lemma)
            print lemmaName, 'at', ln
        elif 'Qed.' in line and lemma in lemmas:
            lemma.length = ln - lemma.length
            lemma = ''

        ln += 1

    print '\n'

print 'Lengths:'
pprint(lemmas)
