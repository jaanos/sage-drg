# -*- coding: utf-8 -*-

refs = {
    "BCN": {
        "type": "book",
        "authors": [("Brouwer", ("Andries", "E.")),
                    ("Cohen", ("Arjeh", "M.")),
                    ("Neumaier", ("Arnold", ))],
        "title": "Distance-regular graphs",
        "series": "Ergebnisse der Mathematik und ihrer Grenzgebiete (3) "
                  "[Results in Mathematics and Related Areas (3)]",
        "volume": 18,
        "publisher": "Springer-Verlag",
        "address": "Berlin",
        "year": 1989,
        "pages": ("xviii", 495)
    },
    "Coolsaet95": {
        "type": "article",
        "authors": [("Coolsaet", ("Kris", ))],
        "title": "Local structure of graphs with "
                r"$\lambda = \mu = 2$, $a_2 = 4$",
        "journal": "Combinatorica",
        "fjournal": "Combinatorica",
        "volume": 15,
        "number": 4,
        "pages": (481, 487),
        "year": 1995
    },
    "Coolsaet05": {
        "type": "article",
        "authors": [("Coolsaet", ("Kris", ))],
        "title": "A distance regular graph with intersection array "
                 "(21, 16, 8; 1, 4, 14) does not exist",
        "journal": "European J. Combin.",
        "fjournal": "European Journal of Combinatorics",
        "volume": 26,
        "number": 5,
        "pages": (709, 716),
        "year": 2005
    },
    u"CoolsaetJurišić08": {
        "type": "article",
        "authors": [("Coolsaet", ("Kris", )), (u"Jurišić", ("Aleksandar", ))],
        "title": "Using equality in the Krein conditions "
                 "to prove nonexistence of certain distance-regular graphs",
        "journal": "J. Combin. Theory Ser. A",
        "fjournal": "Journal of Combinatorial Theory, Series A",
        "volume": 115,
        "number": 6,
        "pages": (1086, 1095),
        "year": 2008
    },
    "DeBruyn10": {
        "type": "article",
        "authors": [("De Bruyn", ("Bart", ))],
        "title": "The nonexistence of regular near octagons with parameters "
                 "$(s, t, t_2, t_3) = (2, 24, 0, 8)$",
        "journal": "Electron. J. Combin.",
        "fjournal": "Electronic Journal of Combinatorics",
        "volume": 17,
        "pages": "R149",
        "year": 2010
    },
    "DeBruynVanhove15": {
        "type": "article",
        "authors": [("De Bruyn", ("Bart", )), ("Vanhove", ("Frederic", ))],
        "title": "On $Q$-polynomial regular near $2d$-gons",
        "journal": "Combinatorica",
        "fjournal": "Combinatorica",
        "volume": 35,
        "number": 2,
        "pages": (181, 208),
        "year": 2015
    },
    "Fon-Der-Flaass93a": {
        "type": "article",
        "authors": [("Fon-Der-Flaass", ("Dmitrii", "Germanovich"))],
        "title": "A distance-regular graph with intersection array "
                 "$(5, 4, 3, 3; 1, 1, 1, 2)$ does not exist",
        "journal": "J. Algebraic Combin.",
        "fjournal": "Journal of Algebraic Combinatorics",
        "volume": 2,
        "number": 1,
        "pages": (49, 56),
        "year": 1993
    },
    "Fon-Der-Flaass93b": {
        "type": "article",
        "authors": [("Fon-Der-Flaass", ("Dmitrii", "Germanovich"))],
        "title": "There exists no distance-regular graph "
                 "with intersection array $(5, 4, 3; 1, 1, 2)$",
        "journal": "European J. Combin.",
        "fjournal": "European Journal of Combinatorics",
        "volume": 14,
        "number": 5,
        "pages": (409, 412),
        "year": 1993
    },
    "Gavrilyuk11": {
        "type": "article",
        "authors": [("Gavrilyuk", ("Alexander", "L."))],
        "title": "Distance-regular graphs with intersection arrays "
                 r"$\{55, 36, 11; 1, 4, 45\}$ and $\{56, 36, 9; 1, 3, 48\}$ "
                 "do not exist",
        "journal": "Dokl. Akad. Nauk",
        "fjournal": "Doklady Akademii Nauk",
        "volume": 439,
        "number": 1,
        "pages": (14, 17),
        "year": 2011
    },
    "GavrilyukMakhnev05": {
        "type": "article",
        "authors": [("Gavrilyuk", ("Alexander", "L.")),
                    ("Makhnev", ("Alexander", "Alexeevich"))],
        "title": "Krein graphs without triangles",
        "journal": "Dokl. Akad. Nauk",
        "fjournal": "Doklady Akademii Nauk",
        "volume": 403,
        "number": 6,
        "pages": (727, 730),
        "year": 2005
    },
    "GavrilyukMakhnev12": {
        "type": "article",
        "authors": [("Gavrilyuk", ("Alexander", "L.")),
                    ("Makhnev", ("Alexander", "Alexeevich"))],
        "title": "Distance-regular graphs with intersection arrays "
                 r"$\{52, 35, 16; 1, 4, 28\}$ and $\{69, 48, 24; 1, 4, 46\}$ "
                 "do not exist",
        "journal": "Des. Codes Cryptogr.",
        "fjournal": "Designs, Codes and Cryptography",
        "volume": 65,
        "number": (1, 2),
        "pages": (49, 54),
        "year": 2012
    },
    "GavrilyukMakhnev13": {
        "type": "article",
        "authors": [("Gavrilyuk", ("Alexander", "L.")),
                    ("Makhnev", ("Alexander", "Alexeevich"))],
        "title": "A distance-regular graph with intersection array "
                 r"$\{45, 30, 7; 1, 2, 27\}$ does not exist",
        "journal": "Diskret. Mat.",
        "fjournal": "Diskretnaya Matematika",
        "volume": 25,
        "number": 2,
        "pages": (13, 30),
        "year": 2013
    },
    "GodsilHensel92": {
        "type": "article",
        "authors": [("Godsil", ("Christopher", "D.")),
                    ("Hensel", ("A.", "D."))],
        "title": "Distance regular covers of the complete graph",
        "journal": "J. Combin. Theory Ser. B",
        "fjournal": "Journal of Combinatorial Theory, Series B",
        "volume": 56,
        "number": 2,
        "pages": (205, 238),
        "year": 1992
    },
    "GodsilKoolen95": {
        "type": "article",
        "authors": [("Godsil", ("Christopher", "D.")),
                    ("Koolen", ("Jacobus", "Hendricus"))],
        "title": "On the multiplicity of eigenvalues "
                 "of distance-regular graphs",
        "journal": "Linear Algebra Appl.",
        "fjournal": "Linear Algebra and its Applications",
        "volume": (226, 228),
        "pages": (273, 275),
        "year": 1995
    },
    "IvanovShpectorov90": {
        "type": "article",
        "authors": [("Ivanov", ("Aleksandr", "Anatol'evich")),
                    ("Shpectorov", ("Sergey", "V."))],
        "title": "The $P$-geometry for $M_{23}$ "
                 "has no nontrivial $2$-coverings",
        "journal": "European J. Combin.",
        "fjournal": "European Journal of Combinatorics",
        "volume": 11,
        "number": 4,
        "pages": (373, 379),
        "year": 1990
    },
    u"JurišićVidali12": {
        "type": "article",
        "authors": [(u"Jurišić", ("Aleksandar", )), ("Vidali", (u"Janoš", ))],
        "title": "Extremal $1$-codes in distance-regular graphs "
                 "of diameter $3$",
        "journal": "Des. Codes Cryptogr.",
        "fjournal": "Designs, Codes and Cryptography",
        "volume": 65,
        "number": (1, 2),
        "pages": (29, 47),
        "year": 2012
    },
    u"JurišićVidali17": {
        "type": "unpublished",
        "authors": [(u"Jurišić", ("Aleksandar", )), ("Vidali", (u"Janoš", ))],
        "title": "Restrictions on classical distance-regular graphs",
        "note": "submitted",
        "year": 2017
    },
    "Koolen92": {
        "type": "article",
        "authors": [("Koolen", ("Jacobus", "H."))],
        "title": "A new condition for distance-regular graphs",
        "journal": "European J. Combin.",
        "fjournal": "European Journal of Combinatorics",
        "volume": 13,
        "number": 1,
        "pages": (63, 64),
        "year": 1992
    },
    "KoolenPark10": {
        "type": "article",
        "authors": [("Koolen", ("Jack", )), ("Park", ("Jongyook", ))],
        "title": "Shilla distance-regular graphs",
        "journal": "European J. Combin.",
        "fjournal": "European Journal of Combinatorics",
        "volume": 31,
        "number": 8,
        "pages": (2064, 2073),
        "year": 2010
    },
    "Lambeck93": {
        "type": "article",
        "authors": [("Lambeck", ("Ernst", ))],
        "title": "Some elementary inequalities for distance-regular graphs",
        "journal": "European J. Combin.",
        "fjournal": "European Journal of Combinatorics",
        "volume": 14,
        "number": 1,
        "pages": (53, 54),
        "year": 1993
    },
    "Urlep12": {
        "type": "article",
        "authors": [("Urlep", (u"Matjaž", ))],
        "title": "Triple intersection numbers of "
                 "$Q$-polynomial distance-regular graphs",
        "journal": "European J. Combin.",
        "fjournal": "European Journal of Combinatorics",
        "volume": 33,
        "number": 6,
        "pages": (1246, 1252),
        "year": 2012
    },
    "Vidali13": {
        "type": "phdthesis",
        "authors": ["Vidali", (u"Janoš", )],
        "title": "Codes in distance-regular graphs",
        "school": "University of Ljubljana",
        "year": 2013
    },
    "Vidali13a": {
        "type": "unpublished",
        "authors": ["Vidali", (u"Janoš", )],
        "title": "There is no distance-regular graph with intersection array "
                 r"$\{55, 54, 50, 35, 10; 1, 5, 20, 45, 55\}$",
        "note": "manuscript",
        "year": 2013
    },
    "Vidali16": {
        "type": "unpublished",
        "authors": ["Vidali", (u"Janoš", )],
        "note": "unpublished result",
        "year": 2016
    }
}
