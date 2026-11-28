# A certificate for three full layers in the seven-cube

## In brief

How many points can a seven-by-seven-by-seven grid hold if no three distinct points lie on a straight line? A coordinate layer can hold at most 14 points, because its seven rows can hold at most two apiece. We check whether 87 points can fit when each coordinate direction has a layer of 14.

Once three full layers are fixed, any site on a line through two of their points is ruled out. Counting the sites that can still fit in each of the other layers usually gives an upper bound below 87. In the remaining cases the checker lists every possible pattern for one additional layer and closes each branch. For example, one triple of full layers at height zero leaves a single 13-point pattern in the layer at $z=3$ if the total is to reach 87. Fixing that pattern reduces the bound to 78 by counting along parallel lines.

The complete replay shows that a set with three full perpendicular layers has at most 86 points. The exact maximum without the layer condition remains open. [Original seven-cube problem](https://arxiv.org/html/2609.25133v1#S3)

## What this settles

Every subset of the seven-cube with no three distinct real-collinear points and a 14-point layer perpendicular to each of the three coordinate axes has at most 86 points, and the unrestricted maximum remains open.

## Why it matters

Focused contribution

The bound adds to the known one-axis layer exclusions by showing that 87 points are impossible with three full perpendicular layers at any heights.

## Replay

Run `python3 -I verify.py` from this directory with Python 3.10 or later. The checker reads [forest.json](forest.json) and prints `PASS` after the complete check. The [proof](PROOF.md) explains how the checker covers every initial case and every necessary branch.
