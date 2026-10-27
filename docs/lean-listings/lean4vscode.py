"""Pygments lexer for Lean 4 with VS Code-like token classes.

Adds to Pygments' Lean4Lexer: the name declared by theorem/def/... is Name.Function; round, square and
curly brackets are Punctuation; anonymous-constructor and other angle brackets are Punctuation.Marker.
Everything else is inherited.
"""
from pygments.lexer import bygroups, inherit
from pygments.lexers.lean import Lean4Lexer
from pygments.token import Keyword, Name, Punctuation, Whitespace

class CustomLexer(Lean4Lexer):
    name = 'Lean 4 (VS Code classes)'
    aliases = ['lean4vscode']
    tokens = {
        'root': [
            (r'(theorem|lemma|def|abbrev|structure|class|inductive|example|opaque|axiom|instance)'
             r'(\s+)([^\s:{(\[\]⟨⟩]+)',
             bygroups(Keyword.Declaration, Whitespace, Name.Function)),
            (r'[()\[\]{}]', Punctuation),
            (r'[⟨⟩⦃⦄‹›⟪⟫]', Punctuation.Marker),
            inherit,
        ],
    }
