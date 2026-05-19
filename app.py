#!/usr/bin/env python3
"""
CDCL SAT Solver Visualizer — Flask backend
Run:  python app.py
Then open:  http://127.0.0.1:5000
"""
from flask import Flask, render_template, request, jsonify
import traceback
import re

app = Flask(__name__)

# ── Default algorithm shown in the editable code editor ──────────────────────
DEFAULT_ALGORITHM = """\
# ════════════════════════════════════════════════════════════════════════
#  ALGORITHM CODE — edit or replace with any solver you like!
#
#  Variables in scope when this runs:
#    clauses   list[list[int]]   CNF formula
#                                positive int = literal, negative = negated
#    num_vars  int
#    var_names list[str]         var_names[i-1] is the name of variable i
#
#  You must assign before the code ends:
#    result      = "SAT" | "UNSAT"
#    assignment  = {var_int: True|False}   (empty dict if UNSAT)
#    steps       = list of step-dicts for the visualiser
#
#  step-dict format:
#    { "nodes": [ {"id": str, "label": str,
#                  "color": hex_str, "shape": str, "level": int}, ... ],
#      "edges": [ {"from": str, "to": str, "label": str}, ... ],
#      "label": str }          ← description shown below the graph
#
#  Shapes:  "diamond" = decision   "dot" = propagation   "square" = conflict ⊥
# ════════════════════════════════════════════════════════════════════════

def solve(clauses, num_vars, var_names):
    clauses = [list(c) for c in clauses]
    assign  = {}   # var -> bool
    lev     = {}   # var -> decision level
    reason  = {}   # var -> antecedent clause (None = decision)
    depth   = {}   # var -> implication depth (used as vis.js level for layout)
    dl      = 0
    steps   = []

    def vn(var, val):
        name = var_names[var - 1] if 0 < var <= len(var_names) else f"x{var}"
        return ("¬" if not val else "") + name

    def impl_depth(var):
        # decisions anchor at dl*100; propagated nodes get parent_max+1
        if reason[var] is None:
            return dl * 100
        parents = [abs(l) for l in reason[var] if abs(l) != var and abs(l) in depth]
        return (max((depth[p] for p in parents), default=dl * 100 - 1) + 1)

    def snapshot(desc, conflict_lits=None):
        nodes, edges = [], []
        for v, val in assign.items():
            nodes.append({
                "id":    vn(v, val),
                "label": vn(v, val),
                "color": "#89b4fa" if reason[v] is None else "#a6e3a1",
                "shape": "diamond" if reason[v] is None else "dot",
                "level": depth[v],
            })
        if conflict_lits is not None:
            conf_depth = max((depth[abs(l)] for l in conflict_lits if abs(l) in depth), default=dl * 100) + 1
            nodes.append({"id": "⊥", "label": "⊥",
                          "color": "#f38ba8", "shape": "square", "level": conf_depth})
        for v, rc in reason.items():
            if rc is None:
                continue
            tgt = vn(v, assign[v])
            for lit in rc:
                av = abs(lit)
                if av != v and av in assign:
                    edges.append({"from": vn(av, assign[av]), "to": tgt, "label": ""})
        if conflict_lits is not None:
            for lit in conflict_lits:
                av = abs(lit)
                if av in assign:
                    edges.append({"from": vn(av, assign[av]), "to": "⊥", "label": ""})
        steps.append({"nodes": nodes, "edges": edges, "label": desc})

    def lit_val(lit):
        v = abs(lit)
        return None if v not in assign else assign[v] == (lit > 0)

    def unit_prop():
        changed = True
        while changed:
            changed = False
            for c in clauses:
                vals = [lit_val(l) for l in c]
                if True in vals:
                    continue
                if all(v is False for v in vals):
                    return c
                unset = [c[i] for i, v in enumerate(vals) if v is None]
                if len(unset) == 1:
                    lit = unset[0]
                    var = abs(lit)
                    assign[var] = lit > 0
                    lev[var]    = dl
                    reason[var] = c
                    depth[var]  = impl_depth(var)
                    snapshot(f"Propagate  {vn(var, assign[var])}  (level {dl})")
                    changed = True
        return None

    def analyze(conf):
        clause = set(conf)
        seen   = set()
        for _ in range(1000):
            at_dl = [l for l in clause
                     if abs(l) in lev and lev[abs(l)] == dl and abs(l) not in seen]
            if len(at_dl) <= 1:
                break
            lit = at_dl[-1]
            var = abs(lit)
            seen.add(var)
            if reason.get(var):
                clause = (clause - {lit, -lit}) | (set(reason[var]) - {lit, -lit})
        learned = list(clause)
        bt_lvls = [lev[abs(l)] for l in learned
                   if abs(l) in lev and lev[abs(l)] < dl]
        return learned, (max(bt_lvls) if bt_lvls else 0)

    def backtrack(to_dl):
        for v in [v for v in list(assign) if lev[v] > to_dl]:
            del assign[v], lev[v], reason[v], depth[v]

    # ── main CDCL loop ───────────────────────────────────────────────────────
    conf = unit_prop()
    if conf is not None:
        snapshot("Conflict at level 0 → UNSAT", conf)
        return "UNSAT", {}, steps

    while True:
        unset = [v for v in range(1, num_vars + 1) if v not in assign]
        if not unset:
            snapshot("All variables assigned → SAT")
            return "SAT", dict(assign), steps

        dl += 1
        var = unset[0]
        assign[var] = True
        lev[var]    = dl
        reason[var] = None
        depth[var]  = impl_depth(var)
        snapshot(f"Decide  {vn(var, True)}  (level {dl})")

        conf = unit_prop()
        if conf is not None:
            snapshot(f"Conflict at level {dl}", conf)
            learned, bt = analyze(conf)
            if dl == 0:
                return "UNSAT", {}, steps
            clauses.append(learned)
            backtrack(bt)
            dl = bt
            lits_str = " ∨ ".join(
                ("¬" if l < 0 else "") + var_names[abs(l) - 1]
                for l in learned if 0 < abs(l) <= len(var_names)
            )
            snapshot(f"Learned  [{lits_str}],  backtrack → level {bt}")
            unit_prop()

result, assignment, steps = solve(clauses, num_vars, var_names)
"""


# ── Formula parser ─────────────────────────────────────────────────────────────
def parse_formula(text: str):
    """
    Parse  (A | B | ~C) & (~A | D)  into (clauses, var_names).
    Supports ~ ! NOT as negation, & AND as clause separator, | OR as literal separator.
    Returns clauses as list[list[int]]; positive = literal, negative = negated.
    """
    text = text.strip()
    raw  = re.findall(r'\b(?!AND\b|OR\b|NOT\b)[A-Za-z]\w*', text)
    seen, var_names = set(), []
    for v in raw:
        if v not in seen:
            seen.add(v)
            var_names.append(v)
    vmap = {v: i + 1 for i, v in enumerate(var_names)}

    clause_strs = re.split(r'\s*&\s*|\s+AND\s+', text)
    clauses = []
    for cs in clause_strs:
        cs = cs.strip().strip('()')
        lit_strs = re.split(r'\s*\|\s*|\s+OR\s+', cs)
        clause = []
        for ls in lit_strs:
            ls  = ls.strip()
            neg = bool(re.match(r'^[~!]|^NOT\s+', ls))
            nm  = re.sub(r'^[~!]\s*|^NOT\s+', '', ls).strip()
            if nm in vmap:
                clause.append(-vmap[nm] if neg else vmap[nm])
        if clause:
            clauses.append(clause)
    return clauses, var_names


# ── Routes ─────────────────────────────────────────────────────────────────────
@app.route('/')
def index():
    return render_template('index.html', default_code=DEFAULT_ALGORITHM)


@app.route('/solve', methods=['POST'])
def solve_endpoint():
    data    = request.get_json(force=True)
    formula = data.get('formula', '').strip()
    code    = data.get('code', '')

    if not formula:
        return jsonify({'error': 'Formula is empty.'})

    try:
        clauses, var_names = parse_formula(formula)
    except Exception:
        return jsonify({'error': f'Parse error:\n{traceback.format_exc()}'})

    if not clauses:
        return jsonify({'error': 'No clauses found — check your formula syntax.'})

    ns = dict(
        clauses   = [list(c) for c in clauses],
        num_vars  = len(var_names),
        var_names = var_names,
        result    = None,
        assignment= {},
        steps     = [],
    )

    try:
        exec(compile(code, '<algorithm>', 'exec'), ns)
    except Exception:
        return jsonify({'error': f'Algorithm error:\n{traceback.format_exc()}'})

    result     = ns.get('result', 'UNKNOWN')
    assignment = ns.get('assignment', {})
    steps      = ns.get('steps', [])

    named = {
        (var_names[v - 1] if 0 < v <= len(var_names) else f'x{v}'): val
        for v, val in assignment.items()
    }

    return jsonify({
        'result':     result,
        'assignment': named,
        'steps':      steps,
        'info':       f'{len(clauses)} clauses · {len(var_names)} variables · {len(steps)} steps',
    })


if __name__ == '__main__':
    print('\n  CDCL Visualizer →  http://127.0.0.1:8080\n')
    app.run(debug=True, port=8080)
