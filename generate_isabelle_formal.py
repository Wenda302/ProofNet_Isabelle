#!/bin/env python3
import sys
import ndjson
import re
import os
import openai
import json

from ratelimit import limits, sleep_and_retry

from tqdm import tqdm

PROMPT = open("prompts/9shot_formalise.txt", "r").read()

@sleep_and_retry
@limits(calls=1, period=60)
def call_api(engine, prompt, max_tokens, n, temperature):
    return openai.Completion.create(
        engine=engine,
        prompt=prompt,
        max_tokens=max_tokens,
        n=n,
        temperature=temperature,
    )

def get_codex_statement(nl_statement,DISABLE_CODEX=False):
    if DISABLE_CODEX:
        return ''
    outs = call_api(engine="code-davinci-002", 
                        prompt=PROMPT+"\nNatural language version: \""+nl_statement+"\" Translate the natural language version to an Isabelle version:", 
                        max_tokens=400, 
                        n=1, 
                        temperature=0
                        )
    text_outs = [x["text"] for x in outs["choices"]]
    trimmed_outs = [x[:x.index("oops")].strip() if "oops" in x else "" for x in text_outs]
    return trimmed_outs[0]

def build_entries(entries_file:str):
    try:
        with open(entries_file) as f:
            entries = json.load(f)
    except:
        with open('informal.jsonl') as f:
            informal = ndjson.load(f)

        with open('id_name_dict.jsonl') as f:
            id_name_dict = ndjson.load(f)

        entries = []
        for informal_line,id_name_dict_line in tqdm(zip(informal,id_name_dict)):
            assert informal_line['id'] == id_name_dict_line['id']
            statement_id = informal_line['id']
            name = id_name_dict_line['name']
            book   = name.split('.', maxsplit=1)[0]
            number = name.split('.', maxsplit=1)[1]
            nl_statement = informal_line['nl_statement']

            with open(os.path.join('lean_formal', book+'.lean'),'r') as f:
                lean_str = f.read()
            
            start_idx = lean_str.find('theorem exercise_' + number.replace('.', '_'))
            if start_idx != -1:
                end_idx = lean_str.find('sorry',start_idx)
                lean_statemennt = lean_str[start_idx:end_idx]
            else:
                lean_statemennt = ''
           
            entry = {}
            entry['id'] = statement_id
            entry['book_name'] = book
            entry['problem_number'] = number.replace('.', '_')
            entry['nl_statement'] = nl_statement
            entry['lean_statement'] =lean_statemennt
            entry['codex_statement'] = ''
            entries.append(entry)

    return entries

entries = build_entries('entries.json')

print(entries)

for entry in tqdm(entries):
    if entry['codex_statement'] == '':
        entry['codex_statement'] = get_codex_statement(entry['nl_statement'],DISABLE_CODEX=False)
        with open( "entries.json" , "w" ) as f:
            json.dump(entries , f)


different_book_names = set()
for entry in entries:
    different_book_names.add(entry['book_name'])


for book_name in different_book_names:

    with open(os.path.join('isabelle_formal',book_name+'.thy'), "w") as f: 
        f.write('theory '+book_name+'\n imports Main\nbegin\n\n')
        for entry in entries:
            if entry['book_name'] == book_name:
                f.write('(*\nproblem_number:'+entry['problem_number'])
                f.write('\nnatural language statement:\n'+entry['nl_statement'])
                f.write('\nlean statement:\n'+entry['lean_statement'])
                f.write('\ncodex statement:\n'+entry['codex_statement'])
                f.write('\nOur comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>\n *)\n')
                f.write('theorem exercise_'+entry['problem_number']+': undefined oops\n\n\n')

        f.write('\n\nend')

print(different_book_names)