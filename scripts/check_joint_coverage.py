#!/usr/bin/env python3
"""Check fresh axiom output for Theorem 1.3 joint coverage and graph wrappers."""
import argparse
from pathlib import Path
from audit_project_axioms import parse_fingerprints, STANDARD_AXIOMS, MI01, DISTANCE_INPUT

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--joint', type=Path, required=True)
parser.add_argument('--graph', type=Path, required=True)
args = parser.parse_args()
prefix = 'SeriesParallel.MainText.'
joint_names = [prefix + 'mainAdmissible_eq_Ici_lambdaStar',
               prefix + 'resistanceSpeedNearCritical',
               prefix + 'GraphSemantics.graphResistanceSpeedNearCritical']
expected_joint = {name: STANDARD_AXIOMS | {MI01} for name in joint_names}
graph_internal = ['SPNetwork.traditionalDistance_realize', 'SPNetwork.traditionalResistance_realize',
                  'GraphSemantics.graphDistanceValue_eq_distanceValue',
                  'GraphSemantics.graphResistanceValue_eq_resistanceValue']
expected_graph = {prefix + name: STANDARD_AXIOMS for name in graph_internal}
for name in ['logarithmicSpeeds', 'firstMomentLogarithmicRates', 'resistanceSpeedNearCritical']:
    axioms = STANDARD_AXIOMS | ({MI01} if name == 'resistanceSpeedNearCritical' else {DISTANCE_INPUT})
    expected_graph[prefix + name] = axioms
    expected_graph[prefix + 'GraphSemantics.graph' + name[0].upper() + name[1:]] = axioms
errors=[]
for title, path, expected in [('joint', args.joint, expected_joint), ('graph', args.graph, expected_graph)]:
    actual = parse_fingerprints(path.read_text(encoding='utf-8'))
    if actual != expected:
        errors.append(f'{title}: fingerprints differ from expected declarations and trust boundary')
for error in errors:
    print('ERROR:',error)
if errors:
    raise SystemExit(1)
print('joint-coverage audit: PASS (3 joint declarations; 10 graph/bridge fingerprints)')
