# Distance-regular graph parameter checking in Sage

A Sage package for checking the feasibility of distance-regular graph parameter sets.
A more detailed description, along with some results, is available in a [manuscript](https://arxiv.org/abs/1803.10797) currently available on arXiv.


## Contents

### `drg`

The `drg` folder contains the package source. After you make sure that Sage sees this folder, you can import it as a Python module.
```python
sage: import drg
sage: p = drg.DRGParameters([80, 63, 12], [1, 12, 60])
sage: p.check_feasible()
```

You can also give an intersection array with parameters.
```python
sage: r = var("r")
sage: fam = drg.DRGParameters([2*r^2*(2*r + 1), (2*r - 1)*(2*r^2 + r + 1), 2*r^2], [1, 2*r^2 , r*(4*r^2 - 1)])
sage: fam.check_feasible()
sage: fam1 = fam.subs(r == 1)
sage: fam1
Parameters of a distance-regular graph with intersection array {6, 4, 2; 1, 2, 3}
sage: fam2 = fam.subs(r == 2)
sage: fam2
Parameters of a distance-regular graph with intersection array {40, 33, 8; 1, 8, 30}
sage: fam2.check_feasible()
...
InfeasibleError: nonexistence by JurišićVidali12
```

### [`jupyter`](jupyter)

A collection of sample Jupyter notebooks giving some nonexistence results.


## Citing

If you use `sage-drg` in your research, please cite the manuscript:

* J. Vidali. Using symbolic computation to prove nonexistence of distance-regular graphs, 2018. [arXiv:1803.10797](http://arxiv.org/abs/1803.10797).

```latex
@other {v18a,
    AUTHOR = {Vidali, Janoš},
     TITLE = {Using symbolic computation to prove nonexistence of distance-regular graphs},
      NOTE = {\href{http://arxiv.org/abs/1803.10797}{\texttt{arXiv:1803.10797}}},
      YEAR = {2018},
}
```
