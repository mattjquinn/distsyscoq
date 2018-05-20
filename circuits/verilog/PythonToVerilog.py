#!/usr/bin/python3

import sys
from antlr4 import *
from antlrgallinaparser import GallinaVisitor, GallinaLexer, GallinaParser

class GallinaTranslator(GallinaVisitor):

    def visitSentences(self, ctx):
        print("[XLATE] visitSentences")
        print(ctx.getText())
        self.visitChildren(ctx)

    def visitTerm(self, ctx):
        print("[XLATE] visitTerm")
        self.visitChildren(ctx)

    def visitInductive(self, ctx):
        print("[XLATE] visitInductive")
        self.visitChildren(ctx)
        ind_name = ctx.ind_body().ID().getText()
        for rule in ctx.ind_body().ind_rule():
          print(rule.const.text)
          print(rule.ty.text)

    def visitDefinition(self, ctx):
        print("[XLATE] visitDefinition")
        self.visitChildren(ctx)
        defn_name = ctx.ID().getText()
        print(defn_name)
        print(ctx.term().getText())

def main(argv):
    input = FileStream(argv[1])
    lexer = GallinaLexer(input)
    stream = CommonTokenStream(lexer)
    stream.fill()
    parser = GallinaParser(stream)
    tree = parser.sentences()
    translator = GallinaTranslator()
    translator.visitSentences(tree)

if __name__ == '__main__':
    main(sys.argv)
