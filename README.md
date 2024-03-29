# Distance-regular graph parameter checking in Sage

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.1418409.svg)](https://doi.org/10.5281/zenodo.1418409)

[![Launch in Binder](https://mybinder.org/badge.svg)](https://mybinder.org/v2/gh/jaanos/sage-drg/master?filepath=index.ipynb)

A [SageMath](https://www.sagemath.org/) package for checking the feasibility of distance-regular graph parameter sets.
A more detailed description, along with some results, is available in a [paper](http://www.combinatorics.org/ojs/index.php/eljc/article/view/v25i4p21) published in the [Electronic Journal of Combinatorics](http://www.combinatorics.org/).


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
Also includes conference and seminar presentations.


## Citing

If you use `sage-drg` in your research, please cite both the paper and the software:

* J. Vidali. Using symbolic computation to prove nonexistence of distance-regular graphs. *Electron. J. Combin.*, 25(4)#P4.21, 2018. [`http://www.combinatorics.org/ojs/index.php/eljc/article/view/v25i4p21`](http://www.combinatorics.org/ojs/index.php/eljc/article/view/v25i4p21).

* J. Vidali. `jaanos/sage-drg`: `sage-drg` v0.9, 2019. [`https://github.com/jaanos/sage-drg/`](https://github.com/jaanos/sage-drg/), [`doi:10.5281/zenodo.1418409`](https://doi.org/10.5281/zenodo.1418409).

You may also want to cite other documents containing descriptions of features that were added since the above paper was written:

* J. Vidali. Computing distance-regular graph and association scheme parameters in SageMath with `sage-drg`. *Sém. Lothar. Combin.* 82B#105, 2019. [`https://www.mat.univie.ac.at/~slc/wpapers/FPSAC2019/105.pdf`](https://www.mat.univie.ac.at/~slc/wpapers/FPSAC2019/105.pdf)
    + support for general and *Q*-polynomial association schemes

* A. L. Gavrilyuk, J. Vidali, J. S. Williford. On few-class *Q*-polynomial association schemes: feasible parameters and nonexistence results, *Ars Math. Contemp.*, 20(1):103-127, 2021. [`doi:10.26493/1855-3974.2101.b76`](https://doi.org/10.26493/1855-3974.2101.b76).
    + triple intersection number solution finder and forbidden quadruples check
    + support for quadruple intersection numbers

### BibTeX

The above citations are given here in BibTeX format.

```latex
@article{v18,
    AUTHOR = {Vidali, Jano\v{s}},
     TITLE = {Using symbolic computation to prove nonexistence of distance-regular graphs},
   JOURNAL = {Electron. J. Combin.},
  FJOURNAL = {Electronic Journal of Combinatorics},
    VOLUME = {25},
    NUMBER = {4},
     PAGES = {P4.21},
      NOTE = {\url{http://www.combinatorics.org/ojs/index.php/eljc/article/view/v25i4p21}},
      YEAR = {2018},
}

@software{v19a,
   AUTHOR = {Vidali, Jano\v{s}},
    TITLE = {{\tt jaanos/sage-drg}: {\tt sage-drg} v0.9},
     NOTE = {\url{https://github.com/jaanos/sage-drg/},
             \href{https://doi.org/10.5281/zenodo.1418409}{\texttt{doi:10.5281/zenodo.1418409}}},
     YEAR = {2019},
}

@article{v19b,
    AUTHOR = {Vidali, Jano\v{s}},
     TITLE = {Computing distance-regular graph and association scheme parameters in SageMath with {\tt sage-drg}},
   JOURNAL = {S\'{e}m. Lothar. Combin.},
  FJOURNAL = {S\'{e}minaire Lotharingien de Combinatoire},
    VOLUME = {82B},
     PAGES = {#105},
      NOTE = {\url{https://www.mat.univie.ac.at/~slc/wpapers/FPSAC2019/105.pdf}},
      YEAR = {2019},
}

@article{gvw21,
    AUTHOR = {Gavrilyuk, Alexander L. and Vidali, Jano\v{s} and Williford, Jason S.},
     TITLE = {On few-class $Q$-polynomial association schemes: feasible parameters and nonexistence results},
   JOURNAL = {Ars Math. Contemp.},
  FJOURNAL = {Ars Mathematica Contemporanea},
    VOLUME = {20},
    NUMBER = {1},
     PAGES = {103--127},
      NOTE = {\href{https://doi.org/10.26493/1855-3974.2101.b76}{\texttt{doi:10.26493/1855-3974.2101.b76}}},
      YEAR = {2021},
}
```
### Other uses

Additionally, `sage-drg` has been used in the following research:

* A. Gavrilyuk, S. Suda and J. Vidali. On tight 4-designs in Hamming association schemes, *Combinatorica*, 40(3):345-362, 2020. [`doi:10.1007/s00493-019-4115-z`](https://doi.org/10.1007/s00493-019-4115-z).

If you would like your research to be listed here, feel free to open an issue or pull request.
