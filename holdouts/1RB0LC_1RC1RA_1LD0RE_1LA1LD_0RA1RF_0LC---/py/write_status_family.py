import json, os
ROOT='/home/user/busy-beaver-explorer/holdouts'
A1='1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---'; A2='1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---'
A3='1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF'; A4='1RB0LE_1RC1RA_1LD0RE_1LA1LD_1LD0RF_0RA---'
ID={A1:155900,A2:72859,A3:123915,A4:66704}; NM={A1:'a1',A2:'a2',A3:'a3',A4:'a4'}
FAM='Chaotic Bell: a (100)^n counter and a list of 1-runs of lengths 6k+1, both growing by 5/4 every two epochs'
P2='holdouts/'+A2
c=lambda s:'<code>%s</code>'%s
INFO={
 A1:dict(far='7.9&times;10<sup>14</sup>',fartxt='7.9x10^14',farfile='data/far_long.json',val='660 tapes up to 2.08&times;10<sup>10</sup> steps',
   haltpat='0 1 1 1',haltlem='fevent_halt',halttr='F1',haltpath='B0 C1 E1 put F on a 1',
   fev='B reading <code>0 1 1 0</code> gives <code>1 1 1 1</code> with B on the right (8 steps: B0 C1 E1 F0 D0 A0 B1 A0)',
   only='F is entered only by E1, E only by C1, and C by B0 (moving right) or A1 (moving left; then C1 puts E on the 0 that A has just written, and E0 goes on)',
   rel='Its F-event differs from the one of the other three machines (it writes <code>1 1 1 1</code> and leaves B, they write <code>1 0 0 0</code> and leave A), so its tapes are not theirs, but the structure and the growth law are the same.',
   tracker='The community tracker calls it &ldquo;Chaotic Bell with a neighbour that halts&rdquo;. Indeed: a1 has E1 = 0RF, F0 = 0LD and a2 has E1 = 1RF, F0 = 0LC; the two mixed tables (E1 = 1RF with F0 = 0LD, and E1 = 0RF with F0 = 0LC) both halt at step 1,272 from blank tape.'),
 A2:dict(far='6.3&times;10<sup>14</sup>',fartxt='6.3x10^14',farfile='data/far_long.json',val='704 tapes up to 2.04&times;10<sup>10</sup> steps',
   haltpat='0 1 1 1',haltlem='fevent_halt',halttr='F1',haltpath='B0 C1 E1 put F on a 1',
   fev='B reading <code>0 1 1 0</code> gives <code>1 0 0 0</code> with A on the right (6 steps: B0 C1 E1 F0 C1 E0)',
   only='F is entered only by E1, E only by C1, and C by B0 (moving right), by A1 (moving left; then C1 puts E on the 0 that A has just written, and E0 goes on) or by F0 (moving left onto the 1 that E1 wrote; then C1 puts E on a 0 again)',
   rel='Machines a2, a3 and a4 share one orbit: a4 has the same list at all 97 visits of the right end up to 10<sup>14</sup> steps, a3 has it too with 5/4 of the step count.',
   tracker='The community tracker says &ldquo;Several tables share one chaotic Bell orbit. The interior is chaotic.&rdquo; The shared orbit is explained below; the two tables between a1 and a2 (E1 = 1RF with F0 = 0LD, and E1 = 0RF with F0 = 0LC) both halt at step 1,272.'),
 A3:dict(far='10<sup>14</sup>',fartxt='10^14',farfile='data/far_1e14.json',val='680 tapes up to 2.02&times;10<sup>10</sup> steps',
   haltpat='0 0 1',haltlem='b_001_halt',halttr='D1',haltpath='B0 C0 put D on a 1',
   fev='B reading <code>0 1 1 0</code> gives <code>1 0 0 0</code> with A on the right (4 steps: B0 C1 F1 F0), and on <code>0 1 1 1 0</code>, where a2 halts, it erases and goes on (<code>fevent_on</code>)',
   only='D is entered only by C0 (moving right), and C by B0 (moving right) or A1 (moving left; then C0 puts D on the 0 that A has just written, and D0 goes on)',
   rel='Machines a2, a3 and a4 share one orbit: the list of a3 at its visits of the right end is the list of a2 (82 of the 97 snapshots of a2 up to 10<sup>14</sup> steps are found literally in the run of a3, the simple comparison used does not match the rest, one of which lies beyond the end of the a3 run), each reached after 5/4 of the step count of a2, a ratio that settles to 1.2500 from 10<sup>10</sup> steps on (a3 does the step C0 of a2 by the detour C0 D0 E1).',
   tracker='The community tracker says &ldquo;Several tables share one chaotic Bell orbit. The interior is chaotic.&rdquo;'),
 A4:dict(far='10<sup>14</sup>',fartxt='10^14',farfile='data/far_1e14.json',val='704 tapes up to 2.04&times;10<sup>10</sup> steps',
   haltpat='0 1 1 1',haltlem='fevent_halt',halttr='F1',haltpath='B0 C1 E1 put F on a 1',
   fev='B reading <code>0 1 1 0</code> gives <code>1 0 0 0</code> with A on the right (4 steps: B0 C1 E1 F0)',
   only='F is entered only by E1, E by C1 (C is entered only by B0) or by A1 (moving left; then E1 puts F on the 0 that A has just written, and F0 goes on)',
   rel='Machines a2, a3 and a4 share one orbit: a4 and a2 have the same list at all 97 visits of the right end up to 10<sup>14</sup> steps (the step counts differ by 2 in 10<sup>7</sup>).',
   tracker='The community tracker says &ldquo;Chaotic Bell. The same table is proved to halt from another start.&rdquo; Started on a blank tape in each of the other five states, the table does not halt in 10<sup>9</sup> steps either, so that start is not a blank-tape start in another state; we did not find which start is meant.'),
}
SNAP=[('5.37&times;10<sup>13</sup>',267238,[439036,53432,87820,10676,17566,2135,3511,426,702,85]),
      ('6.82&times;10<sup>13</sup>',1097580,[133620,219517,26715,43910,5337,8782,1067,1755,213,351]),
      ('8.39&times;10<sup>13</sup>',333950,[548791,66808,109758,13357,21955,2668,4390,533,877,106])]
def table_html():
    h='<div style="overflow-x:auto"><table class="tbl"><thead><tr><th>step (a2)</th><th>n</th>'+''.join('<th>%d</th>'%(6*j+1) for j in range(1,11))+'</tr></thead><tbody>'
    for t,k,g in SNAP: h+='<tr><td>%s</td><td>%s</td>'%(t,format(k,','))+''.join('<td>%s</td>'%format(x,',') for x in g)+'</tr>'
    return h+'</tbody></table></div>'
def table_md():
    s='| step (a2) | n | '+' | '.join(str(6*j+1) for j in range(1,11))+' |\n|'+'---|'*12+'\n'
    for t,k,g in SNAP: s+='| %s | %d | '%(t.replace('&times;','x').replace('<sup>','^').replace('</sup>',''),k)+' | '.join(map(str,g))+' |\n'
    return s
def md(s):
    import re,html
    s=re.sub(r'<code>(.*?)</code>',r'`\1`',s); s=s.replace('<sup>','^').replace('</sup>','')
    s=re.sub(r'</?(b|em|p)>','',s)
    return html.unescape(s).replace('×','x')
for m in (A1,A2,A3,A4):
    I=INFO[m]; p=os.path.join(ROOT,m,'status.json'); d=json.load(open(p)); me=NM[m]
    d['generated']=False; d['group']='G01'; d['family']=FAM
    d['asof']='Status as of 12 November 2026.'
    d['summary']=('A chaotic Bell machine: the head sweeps over a counter (100)^n and a list of runs of 1s of lengths 6k+1; every epoch halves the number of runs of each length while moving them one length up, turns the counter into new runs of 7 and rebuilds the counter, and the whole grows by 5/4 every two epochs. It halts only if state B ever reads %s; not seen in %s steps of an exact accelerated simulation.'%(I['haltpat'],I['fartxt']))
    d['verdict']=['<b>The question is open.</b> The tape holds a counter <code>(100)^n</code> and a list of runs of 1s of lengths 7, 13, 19, &hellip; (6k+1). The run goes in epochs: in each, the number of runs of every length is halved and they move up one length, half the counter becomes new runs of 7, and the new counter is about 5/2 times the old number of runs of 7; so everything grows by 5/4 every two epochs, and the step count by 25/16. These rules hold only up to small corrections (a run more or less, odd runs between the groups), which is why the community calls this a <em>chaotic Bell</em>. The machine halts exactly when state B reads <code>%s</code> (%s; the path is proved in Lean). An exact accelerated simulator, validated against direct simulation, finds no halt in %s steps. %s'%(I['haltpat'],I['haltpath'],I['far'],I['rel'])]
    keep=[c_ for c_ in d['claims'] if c_['title'] not in ('The structure of the tape','Does it halt from blank tape?') and c_['level']!='open' and not c_['title'].startswith(('The local paths','The exact accelerated','No halt in the first '+I['far'],'Neighbours','The epoch law','The shared orbit','Where B reads'))]
    new=[
     {'level':'kernel','title':'The local paths and the halting path','text':'Outside the sweeps, the machine does a handful of local things, each proved for every tape around it: A on a 1 bounces (<code>bounce_on_1</code>, <code>bounce_on_0_0</code>, <code>bounce_on_0_1</code>); %s (<code>fevent</code>, the <em>F-event</em>, twice per round trip in the second half of an epoch); and B reading <code>%s</code> halts: %s (<code>%s</code>). By the table this is the only way to halt: %s.'%(I['fev'],I['haltpat'],I['haltpath'],I['haltlem'],I['only']),'where':'<code>lean/Paths.lean</code>, generated by <code>%s/py/gen_paths.py</code>'%P2},
     {'level':'trusted','title':'The exact accelerated simulator agrees with direct simulation','text':'<code>bell_wsim.py</code> keeps the tape as repeated words, crosses a repeated word in one move (an exact shift rule found on the fly), and at the left turns looks for a stretch of round trips after which the tape has the same shape with counts changed by constants; it then applies many such stretches at once, with the exact step count. Its tape, state and step count were compared with a plain C simulator at %s: all equal.'%I['val'],'where':'<code>%s/py/bell_wsim.py</code>, <code>py/bell_validate.py</code>, <code>c/tapeat.c</code>'%P2},
     {'level':'trusted','title':'No halt in the first %s steps'%I['far'],'text':'The accelerated simulator runs %s steps from blank tape without reaching the halting transition; the list at each visit of the right end is recorded.'%I['far'],'where':'<code>%s/py/bell_farrun.py</code>, <code>holdouts/%s/%s</code>'%(P2,m,I['farfile'])},
     {'level':'trusted','title':'The shared orbit','text':I['rel']+' The reason is in the tables: a4 does with E, F what a2 does with C, E on the bounce of A, a3 replaces the step C0 of a2 by three steps with the same result, and all three turn <code>B&gt; 0 1 1 0</code> into <code>1 0 0 0 A&gt;</code>. They could part only where B reads <code>0 1 0</code> (a2 and a4 differ there: <code>b_010</code>), <code>0 1 1 1</code> (a2 and a4 halt, a3 goes on) or <code>0 0 1</code> (a3 halts); in 10<sup>9</sup> steps of a2 and a4, B never reads <code>0 1 0</code> and reads <code>0 0</code> only at the blank right end.','where':'<code>lean/Paths.lean</code>; <code>data/far_1e14.json</code> of the four machines'},
     {'level':'trusted','title':'Neighbours and other starts','text':I['tracker']+' (Direct runs of 3&times;10<sup>7</sup> steps of every table that differs in one transition, and of the six start states.)','where':'<code>%s/c/neighbours.c</code>'%P2},
     {'level':'heuristic','title':'The epoch law','text':'Read off the recorded lists, not proved: with n the counter and c<sub>7</sub>, c<sub>13</sub>, &hellip; the numbers of runs, one epoch gives c<sub>7</sub>&prime; &asymp; n/2, c<sub>6j+7</sub>&prime; &asymp; c<sub>6j+1</sub>/2 (the half, or one or two less) and n&prime; &asymp; (5/2)&middot;c<sub>7</sub> (within 10<sup>&minus;4</sup> at 10<sup>14</sup> steps). Hence the two interleaved geometric series in the table of counts, the factor 5 per +12 in length, growth by 5/4 every two epochs and step counts growing by 25/16. Between the groups sit a few odd runs that change from epoch to epoch without a visible rule; they are the chaotic part, and the halting pattern can only arise there.','where':'<code>data/far_1e14.json</code>'},
     {'level':'heuristic','title':'Where B reads 0 1 1','text':'In the first 10<sup>9</sup> steps of a2 state B reads <code>0 1 1</code> 20,972 times; in 20,941 of them the cells around are <code>111101[0]110101</code>, in 29 <code>001101[0]110101</code>, and twice (steps 104 and 1,264) something else; the next cell is always 0. a1 has 20,998 such events with the windows <code>111100[0]110101</code> and <code>001100[0]110101</code>. So after the first 1,300 steps the F-events seen are all of two harmless kinds; whether that holds for ever is the open question.','where':'direct C runs (not kept in the repository)'},
     {'level':'open','title':'Does it halt from blank tape?','text':'Not known. It halts exactly if B ever reads <code>%s</code>. A proof of non-halting needs an invariant for the odd runs between the groups, which no closed rule describes so far; the simulator slows down beyond 10<sup>15</sup> steps because those runs pile up at the right end.'%I['haltpat'],'where':''},
    ]
    d['claims']=keep+new
    chk=[x for x in d['check'] if 'bell_' not in x and 'gen_paths' not in x]
    chk+=['python3 %s/py/gen_paths.py --check'%P2,'python3 %s/py/bell_farrun.py %s 1e12     # the accelerated run, about two minutes'%(P2,m)]
    d['check']=chk
    ex=d['explainer']
    ex['lede']='Nobody knows. The head sweeps over a counter and a list of runs of 1s; in every epoch each group of runs is halved and moved up one length, and the counter is rebuilt, so that everything grows by 5/4 every two epochs. It stops only if state B ever reads <code>%s</code>, which has not happened in %s steps.'%(I['haltpat'],I['far'])
    ex['facts']=[{'level':'trusted','value':'%s steps'%I['far'],'text':'No halt in the exact accelerated simulation.'},
                 {'level':'kernel','value':'B&gt; %s'%I['haltpat'],'text':'The only pattern that halts it; the path is proved in Lean.'},
                 {'level':'heuristic','value':'&times;5/4','text':'Growth of the counter and of every group of runs over two epochs.'}]
    shape=[s for s in ex['sections'] if s['id']=='shape']
    secs=[
     {'id':'list','eyebrow':'What it does','heading':'A counter and runs of 1s whose lengths step by 6','html':[
       '<p>After a sweep to the right the tape is a counter <code>(100)^n</code> followed by runs of 1s separated by <code>00</code>; almost all runs have a length 6k+1 and they are sorted into groups: all the 7s, then the 13s, the 19s and so on, with a few odd runs between the groups. After a sweep to the left the same list is written differently: the counter is <code>(011)^n</code> and a run of length v is an alternating stretch <code>0101&hellip;0</code> of v cells, with <code>11</code> between stretches.</p>',
       '<p>The head goes back and forth over all of it. Its right turning point (the <em>front</em>) moves slowly to the right through the list; behind it the runs are regrouped two by two into units that contain a <em>timer</em>, a run of 1s that loses 3 cells on every round trip and so tells the front when to move on. A unit made of runs of length 6j+1 holds the front for about 3(j&minus;1) round trips (one trip for the 7s), and leaves one run of length 6j+7: the group is halved and moved up one length.</p>',
       table_html(),
       '<p>The table shows the counter n and the number of runs of each length at three successive visits of the right end. Follow a column one step down and one step right: it is halved (439,036 &rarr; 219,517 &rarr; 109,758). The new 7s are half the old counter (267,238 &rarr; 133,620), and the new counter is 5/2 of the old 7s (439,036 &rarr; 1,097,580). So two rows down everything is 5/4 as large, and the counts fall by a factor 5 for every 12 added to the length.</p>']},
     {'id':'epoch','eyebrow':'The cycle','heading':'Two phases per epoch','html':[
       '<p><b>Phase 1.</b> The head turns at the left end of the tape; every round trip adds 2 to the counter and moves the front. When the front reaches the right end of the tape, one sweep to the left regroups the whole list.</p>',
       '<p><b>Phase 2.</b> Now the head turns at the right end of the counter: every round trip takes 2 from the counter and makes one new run of 7. In each of these trips state B reads <code>0 1 1 0</code> twice (the <em>F-event</em>): %s. When the counter is used up, phase 1 starts again.</p>'%I['fev'],
       '<p>%s</p>'%I['rel'],
       '<p>The halving is not exact: a group sometimes loses a run, and the odd runs between the groups change from epoch to epoch with no visible rule. That is the chaotic part. Because no pattern repeats, the simulator of this family finds its shortcuts on the fly: it notices that a stretch of round trips repeats with the counts changing by constants and applies many of them at once.</p>']},
     {'id':'halt','eyebrow':'Halting','heading':'What would make it stop','html':[
       '<p>It halts exactly when state B reads <code>%s</code>: %s (%s is the missing transition). Lean checks this path; that there is no other follows from the table: %s.</p>'%(I['haltpat'],I['haltpath'],I['halttr'],I['only']),
       '<p>In the run this has not happened in %s steps. %s</p>'%(I['far'],I['tracker'])]},
    ]
    ex['sections']=secs+shape
    json.dump(d,open(p,'w'),indent=1,ensure_ascii=False); open(p,'a').write('\n')
    # README
    g=m.split('_'); rows='\n'.join('| %s | %s | %s |'%('ABCDEF'[i],x[:3],x[3:]) for i,x in enumerate(g))
    R=[]
    R.append('# %s\n\nbbchallenge id %d (%s of the family). One of the six-state holdouts whose halting from blank tape is open.\n\n| state | read 0 | read 1 |\n|---|---|---|\n%s\n'%(m,ID[m],me,rows))
    R.append('**Family:** %s.\n\n%s\n'%(FAM,d['summary']))
    R.append('## Family\n\nFour G01 machines: `%s` (a1, id 155900), `%s` (a2, id 72859), `%s` (a3, id 123915) and\n`%s` (a4, id 66704). The shared tools live in the folder of a2 (`%s/py`, `c`).\n\n%s\n\n%s\n'%(A1,A2,A3,A4,P2,md(I['rel']),md(I['tracker'])))
    R.append('''## What it does

After a sweep to the right the tape is a counter `(100)^n` followed by runs of 1s separated by `00` (R-form); almost
all runs have a length 6k+1, sorted into groups (the 7s, the 13s, the 19s, ...), with a few odd runs between the
groups. After a sweep to the left the same list reads: counter `(011)^n`, a run of length v is an alternating stretch
`0101...0` of v cells, `11` between stretches (L-form).

The head goes back and forth over the whole tape. Its right turning point (the front) moves to the right through the
list; behind it the runs are regrouped two by two into units with a timer (a run of 1s that loses 3 cells per round
trip: `bounce_on_1`). A unit made of runs 6j+1 holds the front for about 3(j-1) trips (1 trip for the 7s) and leaves
one run 6j+7.

An epoch has two phases. Phase 1: the head turns at the left end of the tape, each round trip adds 2 to n; when the
front reaches the right end, one left sweep regroups the list. Phase 2: the head turns at the right end of the
counter, each round trip takes 2 from n and makes one new run of 7, with two F-events (B reads `0 1 1 0`) per trip;
when the counter is used up, phase 1 resumes.

Counter and numbers of runs at three successive visits of the right end (a2; a1 has other numbers, the same law):

''' + table_md() + '''
Epoch law (read off the data, heuristic): c7' ~ n/2, c(6j+7)' ~ c(6j+1)/2 (the half or one or two less),
n' ~ (5/2) c7. So over two epochs everything grows by 5/4, the step count by 25/16, and the counts fall by 5 for every
+12 in length. The corrections and the odd runs between the groups follow no visible rule: the chaotic part.
''')
    R.append('## Halting condition\n\nIt halts exactly when state B reads `%s`: %s (`%s` in `lean/Paths.lean`). No other way: %s.\n\n%s\nNot seen in %s steps. Whether it can happen is open: one would need an invariant for the odd runs between the groups.\n'%(I['haltpat'],md(I['haltpath']),I['haltlem'],md(I['only']),md(d['claims'][-2]['text'])+'\n',I['fartxt']))
    R.append('''## Reproduce

```sh
P=%s
python3 $P/py/bell_farrun.py %s 1e12                 # exact accelerated run, lists at the right end
gcc -O2 -o /tmp/tapeat $P/c/tapeat.c
python3 $P/py/bell_validate.py %s 2e10 50 /tmp/tapeat   # compare with direct simulation
gcc -O2 -o /tmp/nb $P/c/neighbours.c && /tmp/nb %s 30000000      # neighbours and other start states that halt
python3 $P/py/gen_paths.py --check                    # lean/Paths.lean of the four machines is up to date
```

`%s` holds the recorded lists (`"epochs"`: step, then the tape left of the head as run lengths, `7x12` = twelve runs
of 7, `1xN` = the counter).

## Further work

1. Prove the round trips of both phases for all counts (bbtools.symtm can do each sweep; the regrouping sweep is the
   hard one), then the epoch law with its corrections.
2. Understand the odd runs between the groups; only they can produce the halting pattern.
3. The simulator does not compress the runs that pile up at the right end (`66 1 66 1 ...`), which limits it to about
   10^15 steps; nested jumps would go further.
''' % (P2,m,m,m,I['farfile']))
    lv=lambda c_: '| %s | **%s.** %s | %s |'%(c_['level'],md(c_['title']),md(c_['text']).replace('|','\\|'),md(c_['where']).replace('|','\\|'))
    R.append('## What is proved, and how firmly\n\n| level | claim | where |\n|---|---|---|\n'+'\n'.join(lv(c_) for c_ in d['claims'])+'\n')
    R.append('''## Lean

`lean/Rules.lean` (shift rules, from the first pass, generated by
`holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py`) and `lean/Paths.lean` (the local paths and the
halting path, generated by `%s/py/gen_paths.py`) are listed in `lean/check.sh` after `Blank.lean`:

```sh
. /etc/profile.d/lean.sh && holdouts/%s/lean/check.sh
```

## Pages

- [`pages/holdouts/%s/explainer.html`](../../pages/holdouts/%s/explainer.html)
- [`pages/holdouts/%s/proof-status.html`](../../pages/holdouts/%s/proof-status.html)
''' % (P2,m,m,m,m,m))
    open(os.path.join(ROOT,m,'README.md'),'w').write('\n'.join(R))
    print('updated',m)
