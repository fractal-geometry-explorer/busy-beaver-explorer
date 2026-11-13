"""The family of four machines that share the (0001)-counter: their parameters for the Lean generator and the
simulators.  Identical copies of this file live in each machine's py/ folder."""
DIG = {'a': '0011', 'b': '0011001', 'c': '001101', 'd': '00111', 'e': '00101'}

FAMILY = {
    '1RB0LD_0LB1RC_0RD---_1RE0RF_1LF0RA_0LA0LF': dict(
        ns='H54516', S='D', R='B', near='A', halt_state='C',
        near_desc='A writes a 1 and moves right, B reads that 1 and moves right in state C, and C halts on a 1 (in the '
                  'usual case <code>A&gt;0 0</code>, B steps back onto the new 1 and C then reads the 0)',
        reach=(1010696, 148, [('e', 102), ('e', 319), ('e', 33), ('a', 12)], '001', 0), counted=282,
        costs=dict(W=12, g0=12, visit=11, d=12, dk=30, bounce=32),
        plain='99.990%', nonplain13='260', visits13='2,631,785',
        windows=[(5236, 50), (2012, 22)],
        window_titles=['Carries and an overflow (visits 5,236 to 5,285)', 'Two e collide (visits 2,012 to 2,033)'],
        window_notes=['The lowest digit cycles a, b, c, d, e; on each d to e the carry reaches the next digit. At visit '
                      '5,270 every digit is d: the carry runs into the wall, the d become empty digits z, and a new '
                      'digit is born at the left end.',
                      'The lowest digit catches the next one: the gap between them reaches 0 at visit 2,020 and the pair '
                      'forms compound words (red outline). At visit 2,024 they are two e side by side; the next visit '
                      'contains the near miss and fuses them into one d.'],
        crowd='210 of 2,000', births='23 of the 33',
        piece_steps=dict(start='6n+5', carry='6m+13', bounce='32', left_gap='6k', left_d='17', left_end='6'),
        runs=dict(near15=12, far_html='10<sup>17</sup>', far_md='10^17', far_visits='272,935,363', near_far=15)),
    '1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LA---': dict(
        ns='H59221', S='A', R='E', near='D', halt_state='F',
        near_desc='D writes a 1 and moves right, E reads that 1, erases it and moves right in state F, and F halts on '
                  'a 1 (in the usual case <code>D&gt;0 0</code>, E reads the 0 and goes on in state A)',
        costs=dict(W=10, g0=10, visit=11, d=10, dk=24, bounce=24),
        piece_steps=dict(start='4n+5', carry='4m+9', bounce='24', left_gap='6k', left_d='15', left_end='6'),
        reach=(1001215, 234, [('a', 222), ('e', 88), ('b', 88), ('c', 6)], '001', 0), counted=198,
        plain='99.988%', nonplain13='315', visits13='2,570,989', births='16 of the 46', crowd='633 of 2,000',
        windows=[(4319, 50), (3201, 22)],
        window_titles=['Carries and an overflow (visits 4,319 to 4,368)', 'Two e collide (visits 3,201 to 3,222)'],
        window_notes=['The lowest digit cycles a, b, c, d, e; on each d to e the carry reaches the next digit. At visit '
                      '4,353 every digit is d: the carry runs into the wall, the d become empty digits z, and a new '
                      'digit is born at the left end.',
                      'The lowest digit catches the next one and the pair forms compound words (red outline). At visit '
                      '3,213 they are two e side by side; the next visit contains the near miss, and the pair becomes the word 001 while a new digit is born at the left end.'],
        runs=dict(near15=8, far_html='10<sup>16</sup>', far_md='10^16', far_visits='75,701,323', near_far=9)),
    '1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LC---': dict(
        ns='H19849', S='A', R='E', near='D', halt_state='F',
        near_desc='D writes a 1 and moves right, E reads that 1, erases it and moves right in state F, and F halts on '
                  'a 1 (in the usual case <code>D&gt;0 0</code>, E reads the 0 and goes on in state A)',
        costs=dict(W=10, g0=10, visit=11, d=10, dk=24, bounce=24),
        piece_steps=dict(start='4n+5', carry='4m+9', bounce='24', left_gap='6k', left_d='15', left_end='6'),
        reach=(1001057, 364, [('e', 68), ('a', 71), ('b', 40), ('b', 8)], '001', 0), counted=186,
        plain='99.992%', nonplain13='205', visits13='2,453,542', births='17 of the 27', crowd='171 of 2,000',
        windows=[(6073, 50), (1508, 22)],
        window_titles=['Carries and an overflow (visits 6,073 to 6,122)', 'Two e collide (visits 1,508 to 1,529)'],
        window_notes=['The lowest digit cycles a, b, c, d, e; on each d to e the carry reaches the next digit. At visit '
                      '6,107 every digit is d: the carry runs into the wall, the d become empty digits z, and a new '
                      'digit is born at the left end.',
                      'The lowest digit catches the next one and the pair forms compound words (red outline). At visit '
                      '1,520 they are two e side by side; the next visit contains the near miss, and the pair becomes a single empty digit z.'],
        runs=dict(near15=6, far_html='10<sup>16</sup>', far_md='10^16', far_visits='103,085,042', near_far=6)),
    '1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RA---': dict(
        ns='H45197', S='A', R='E', near='D', halt_state='F',
        near_desc='D writes a 1 and moves right, E reads that 1, erases it and moves right in state F, and F halts on '
                  'a 1 (in the usual case <code>D&gt;0 0</code>, E reads the 0 and goes on in state A)',
        costs=dict(W=10, g0=10, visit=11, d=10, dk=24, bounce=24),
        piece_steps=dict(start='4n+5', carry='4m+9', bounce='24', left_gap='6k', left_d='15', left_end='6'),
        reach=(1000557, 246, [('a', 219), ('b', 86), ('b', 46), ('c', 6)], '001', 0), counted=188,
        plain='99.991%', nonplain13='217', visits13='2,508,051', births='18 of the 27', crowd='175 of 2,000',
        windows=[(3252, 50), (7846, 22)],
        window_titles=['Carries and an overflow (visits 3,252 to 3,301)', 'Two e collide (visits 7,846 to 7,867)'],
        window_notes=['The lowest digit cycles a, b, c, d, e; on each d to e the carry reaches the next digit. At visit '
                      '3,286 every digit is d: the carry runs into the wall, the d become empty digits z, and a new '
                      'digit is born at the left end.',
                      'The lowest digit catches the next one and the pair forms compound words (red outline). At visit '
                      '7,858 they are two e side by side; the next visit contains the near miss, and the pair becomes a single e.'],
        runs=dict(near15=7, far_html='10<sup>16</sup>', far_md='10^16', far_visits='70,410,521', near_far=9)),
}

# what the visit to two adjacent e digits (at the start of the tape) leaves: the end of the rule, and in words
MERGE = {
    '1RB0LD_0LB1RC_0RD---_1RE0RF_1LF0RA_0LA0LF': (
        '0 0 (0001)^n+3 00111 (0001)^m R', 'the pair becomes one digit `d` (value 4), three `W` further right.'),
    '1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LA---': (
        '0 0 0011 (0001)^n+3 001 (0001)^m R',
        'the pair becomes the word `001`, and a new digit `a` is born at the left end of the tape.'),
    '1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LC---': (
        '0 0 (0001)^n+3 0 (0001)^m+1 R', 'the pair becomes a single `0` (an empty digit, a phase defect `00001`).'),
    '1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RA---': (
        '0 0 (0001)^n+3 00101 (0001)^m R', 'the pair becomes one digit `e` (value 0).'),
}

def pieces(S, R):
    """The nine piece rules as symtm (start, end, doc)."""
    return [
        ('start', f'0^inf {S}> 0 0 (0001)^n R', f'0^inf (1010)^n 1 {R}> 0 0 1 R',
         'From the sample configuration the head crosses the left gap `W^n` and arrives at the first digit.'),
        ('carry', f'L 1 {R}> 0 0 1 00111 (0001)^m R', f'L 1 0 1 0 1 (1010)^m 1 {R}> 0 0 1 R',
         'A `d` is passed (the carry): the head crosses it and the gap `W^m` after it, and arrives at the next digit.'),
        ('bounce_a', f'L 1 {R}> 0 0 1 0011 0001 R', f'L 1 0 1 {S}> 0 0 0011001 R', '`a W` becomes `b`, and the head turns.'),
        ('bounce_b', f'L 1 {R}> 0 0 1 0011001 0001 R', f'L 1 0 1 {S}> 0 0 001101 0001 R', '`b W` becomes `c W`.'),
        ('bounce_c', f'L 1 {R}> 0 0 1 001101 0001 R', f'L 1 0 1 {S}> 0 0 00111 0001 R', '`c W` becomes `d W`.'),
        ('bounce_e', f'L 1 {R}> 0 0 1 00101 0001 R', f'L 1 0 1 {S}> 0 0 0001 0011 R', '`e W` becomes `W a`.'),
        ('left_gap', f'L (1010)^k 1 0 1 {S}> 0 0 R', f'L 1 0 1 {S}> 0 0 (0001)^k R',
         'Moving left, the head turns a crossed gap back into `W^k`.'),
        ('left_d', f'L 1 0 1 0 1 1 0 1 {S}> 0 0 R', f'L 1 0 1 {S}> 0 0 00101 R', 'Moving left, a passed `d` becomes `e`.'),
        ('left_end', f'0^inf 1 0 1 {S}> 0 0 R', f'0^inf {S}> 0 0 0001 R',
         'At the left end the tape grows: the next sample configuration, with one more `W`.'),
    ]

def merge_rule(M):
    S = FAMILY[M]['S']
    end, desc = MERGE[M]
    return ('merge_ee', f'0^inf {S}> 0 0 (0001)^n 00101 00101 (0001)^m+1 R', f'0^inf {S}> {end}',
            'Two adjacent `e` digits after the left gap `W^n`: ' + desc)
