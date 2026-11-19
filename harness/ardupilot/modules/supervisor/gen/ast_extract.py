#!/usr/bin/env python3
"""Read the declarations of classes from clang's JSON AST, for the stand-in generator.

  python3 -I ast_extract.py RSP_FILE ARDUCOPTER_DIR OUT_JSON CLASS...

Runs clang (-fsyntax-only, the supervisor's flags from RSP_FILE) on a unit that includes
ArduCopter's Copter.h, dumps the AST filtered to each class, and keeps the complete definition of
each class: its methods (mangled name, name, kind, return type, parameter types and names,
const/virtual/pure/static, defined in the header or not, access) and its fields (name, type,
access, static). Output: {class: {"bases": [...], "methods": [...], "fields": [...], "file": h}}.
"""
import json, os, subprocess, sys, tempfile

RSP, ACDIR, OUT, CLASSES = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]


def dump(cls):
    with tempfile.TemporaryDirectory() as td:
        tu = os.path.join(td, 'tu.cpp')
        open(tu, 'w').write('#include "Copter.h"\n')
        r = subprocess.run(['clang++', '@' + RSP, '-I' + ACDIR, '-fsyntax-only',
                            '-Xclang', '-ast-dump=json', '-Xclang', '-ast-dump-filter',
                            '-Xclang', cls, tu], capture_output=True, text=True)
    txt, dec, i, objs = r.stdout, json.JSONDecoder(), 0, []
    while i < len(txt):
        while i < len(txt) and txt[i] in ' \n\r\t':
            i += 1
        if i >= len(txt):
            break
        if txt.startswith('Dumping', i):
            i = txt.index('\n', i) + 1
            continue
        o, i = dec.raw_decode(txt, i)
        objs.append(o)
    return objs


def has_body(m):
    return any(c.get('kind') == 'CompoundStmt' for c in m.get('inner', []))


def summarize(rec):
    out = {'file': rec['loc'].get('file', ''), 'methods': [], 'fields': [],
           'bases': [b['type']['qualType'] for b in rec.get('bases', [])]}
    access = 'private' if rec.get('tagUsed') == 'class' else 'public'
    for d in rec.get('inner', []):
        k = d.get('kind')
        if k == 'AccessSpecDecl':
            access = d['access']
        elif k in ('CXXMethodDecl', 'CXXConstructorDecl', 'CXXDestructorDecl'):
            if d.get('isImplicit'):
                continue
            ty = d['type']['qualType']
            params = [(p.get('name', ''), p['type']['qualType'])
                      for p in d.get('inner', []) if p.get('kind') == 'ParmVarDecl']
            out['methods'].append({
                'name': d['name'], 'kind': k, 'mangled': d.get('mangledName', ''),
                'type': ty, 'ret': ty.split('(')[0].strip() if k == 'CXXMethodDecl' else '',
                'params': params, 'const': ty.rstrip().endswith('const'),
                'virtual': bool(d.get('virtual')), 'pure': bool(d.get('pure')),
                'static': d.get('storageClass') == 'static', 'body': has_body(d),
                'access': access, 'deleted': bool(d.get('explicitlyDeleted')),
                'defaulted': bool(d.get('explicitlyDefaulted')),
                'variadic': bool(d.get('variadic'))})
        elif k == 'FieldDecl':
            out['fields'].append({'name': d.get('name', ''), 'type': d['type']['qualType'],
                                  'access': access, 'static': False})
        elif k == 'VarDecl':
            out['fields'].append({'name': d.get('name', ''), 'type': d['type']['qualType'],
                                  'access': access, 'static': True,
                                  'mangled': d.get('mangledName', ''),
                                  'init': 'init' in d or bool(d.get('constexpr'))})
    return out


def main():
    res = {}
    for cls in CLASSES:
        for o in dump(cls):
            if (o.get('kind') == 'CXXRecordDecl' and o.get('name') == cls.split('::')[-1]
                    and o.get('completeDefinition')):
                res[cls] = summarize(o)
                break
        else:
            print('ast_extract: no definition of', cls, file=sys.stderr)
    json.dump(res, open(OUT, 'w'), indent=1)


main()
