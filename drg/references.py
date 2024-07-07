import re
from sage.structure.sage_object import SageObject


refs = {}


class Reference(SageObject):
    """
    A class for references.
    """
    DELIMITERS = {}

    def __init__(self, name, **fields):
        """
        Object constructor.
        """
        self.name = name
        self.fields = fields
        refs[name] = self

    def __eq__(self, other):
        """
        Check equality.

        Compares the name with the given object.
        """
        return self.name == other

    def __getattr__(self, name):
        """
        Attribute access method.

        Provides method access for reference fields.
        """
        if name not in self.fields:
            raise AttributeError
        return lambda bibtex=False: \
            self.range(name, self.DELIMITERS.get(name,
                                                 "--" if bibtex else "-"))

    def __getitem__(self, name):
        """
        Item access method.

        Delegates to attribute access.
        """
        return getattr(self, name)()

    def __hash__(self):
        """
        Return the hash value.
        """
        return hash(self.name)

    def __repr__(self):
        """
        String representation.
        """
        return f"{self.__class__.__name__}({self.name})"

    def __str__(self):
        """
        Print representation.
        """
        return self.name

    def author(self, bibtex=False, short=False):
        """
        Return the author(s).
        """
        abbrv = (lambda s: "%s." % s[0]) if short else (lambda s: s)
        authors = ["{}{}".format(("%s " % " ".join(abbrv(name)
                                                   for name in first))
                                 if first else "", last)
                   for last, first in self.fields["author"]]
        if not bibtex and len(authors) > 2:
            authors[:-1] = [", ".join(authors[:-1])]
        return " and ".join(authors)

    def bibtex(self):
        """
        Return the BibTeX string.
        """
        return "@{}{{{}\n{}}}\n".format(self.__class__.__name__.lower(),
                                        self.name,
                                        "".join("%11s = {%s},\n" %
                                                (key,
                                                 getattr(self,
                                                         key)(bibtex=True))
                                                for key in self.fields))

    def range(self, name, delim):
        """
        Insert the given delimiter if the named field is a tuple.

        Otherwise, returns the data unchanged.
        """
        data = self.fields[name]
        if isinstance(data, tuple):
            left, right = data
            return f"{left}{delim}{right}"
        else:
            return data

    def title(self, bibtex=False):
        """
        Return the title.
        """
        if bibtex:
            return re.sub(r'((?<!^)[A-Z]+|\$+[^$]*[A-Z][^$]*\$+)', r'{\1}',
                          self.fields["title"])
        return self.fields["title"]

    authors = author


class Article(Reference):
    """
    A class for articles.
    """
    pass


class Book(Reference):
    """
    A class for books.
    """
    DELIMITERS = {"pages": "+"}


class InCollection(Article):
    """
    A class for articles in a collection.
    """
    pass


class Misc(Article):
    """
    A class for miscellaneous entries (e.g., web pages).
    """
    pass


class PhDThesis(Book):
    """
    A class for PhD theses.
    """
    pass


class Unpublished(Article):
    """
    A class for unpublished papers (including preprints).
    """
    pass


Article("AzarijaMarc18",
        author=[("Azarija", ("Jernej", )), ("Marc", ("Tilen", ))],
        title="There is no (75,32,10,16) strongly regular graph",
        journal="Linear Algebra Appl.",
        fjournal="Linear Algebra and its Applications",
        volume=557,
        pages=(62, 83),
        url="https://doi.org/10.1016/j.laa.2018.07.019",
        year=2018
)

Article("AzarijaMarc20",
        author=[("Azarija", ("Jernej", )), ("Marc", ("Tilen", ))],
        title="There is no (95,40,12,20) strongly regular graph",
        journal="J. Combin. Des.",
        fjournal="Journal of Combinatorial Designs",
        volume=28,
        number=4,
        pages=(294, 306),
        url="https://doi.org/10.1002/jcd.21696",
        year=2020
)

Book("BCN",
     author=[("Brouwer", ("Andries", "E.")),
              ("Cohen", ("Arjeh", "M.")),
              ("Neumaier", ("Arnold", ))],
     title="Distance-regular graphs",
     series="Ergebnisse der Mathematik und ihrer Grenzgebiete (3) "
            "[Results in Mathematics and Related Areas (3)]",
     volume=18,
     publisher="Springer-Verlag",
     address="Berlin",
     year=1989,
     url="https://doi.org/10.1007/978-3-642-74341-2",
     pages=("xviii", 495)
)

Misc("BCN94",
     author=[("Brouwer", ("Andries", "E.")), ("Cohen", ("Arjeh", "M.")),
              ("Neumaier", ("Arnold", ))],
     title="Corrections and additions to the book `Distance-regular graphs'",
     year=1994,
     url="http://www.win.tue.nl/~aeb/drg/"
)

Article("BGK19",
        author=[("Bang", ("Sejeong", )), ("Gavrilyuk", ("Alexander", "L.")),
                 ("Koolen", ("Jack", "H."))],
        title="Distance-regular graphs without $4$-claws",
        journal="European J. Combin.",
        fjournal="European Journal of Combinatorics",
        volume=80,
        pages=(120, 142),
        url="https://doi.org/10.1016/j.ejc.2018.02.022",
        year=2019
)

Article("BHMW89",
        author=[("Bussemaker", ("Frans", "C.")),
                 ("Haemers", ("Willem", "H.")),
                 ("Mathon", ("Rudolf", "A.")),
                 ("Wilbrink", ("Hendrikus", "Adrianus"))],
        title="A $(49, 16, 3, 6)$ strongly regular graph does not exist",
        journal="European J. Combin.",
        fjournal="European Journal of Combinatorics",
        volume=10,
        number=5,
        pages=(413, 418),
        url="https://doi.org/10.1016/S0195-6698(89)80014-9",
        year=1989
)

Article("BSW16",
        author=[("Brouwer", ("Andries", "E.")), ("Sumalroj", ("Supalak", )),
                 ("Worawannotai", ("Chalermpong", ))],
        title="The nonexistence of distance-regular graphs "
              r"with intersection arrays $\{27,20,10;1,2,18\}$ "
              r"and $\{36,28,4;1,2,24\}$",
        journal="Australas. J. Combin.",
        fjournal="The Australasian Journal of Combinatorics",
        volume=66,
        pages=(330, 332),
        url="http://ajc.maths.uq.edu.au/pdf/66/ajc_v66_p330.pdf",
        year=2016
)

Article("BondarenkoRadchenko13",
        author=[("Bondarenko", ("Andriy", "V.")),
                 ("Radchenko", ("Danylo", "V."))],
        title=r"On a family of strongly regular graphs with $\lambda = 1$",
        journal="J. Combin. Theory Ser. B",
        fjournal="Journal of Combinatorial Theory, Series B",
        volume=103,
        number=4,
        pages=(521, 531),
        url="https://doi.org/10.1016/j.jctb.2013.05.005",
        year=2013
)

InCollection("BMPRV18",
             author=[("Bondarenko", ("Andriy", "V.")),
                      ("Mellit", "A."),
                      ("Prymak", ("Andriy", "V.")),
                      ("Radchenko", ("Danylo", )),
                      ("Viazovska", ("Maryna", "S."))],
             title="There is no strongly regular graph with parameters "
                   "(460, 153, 32, 60)",
             booktitle="Contemporary computational mathematics -- "
                       "a celebration of the 80th birthday of Ian Sloan",
             publisher="Springer",
             address="Cham",
             volume=(1, 2),
             pages=(131, 134),
             url="https://doi.org/10.1007/978-3-319-72456-0_7",
             year=2018
)

Article("BPR17",
        author=[("Bondarenko", ("Andriy", "V.")),
                 ("Prymak", ("Andriy", "V.")),
                 ("Radchenko", ("Danylo", ))],
        title="Non-existence of $(76,30,8,14)$ strongly regular graph",
        journal="Linear Algebra Appl.",
        fjournal="Linear Algebra and its Applications",
        volume=527,
        pages=(53, 72),
        url="https://doi.org/10.1016/j.laa.2017.03.033",
        year=2017
)

Article("BrouwerKoolen99",
        author=[("Brouwer", ("Andries", "E.")), ("Koolen", ("Jack", "H."))],
        title="The distance-regular graphs of valency four",
        journal="J. Algebraic Combin.",
        fjournal="Journal of Algebraic Combinatorics",
        volume=10,
        number=1,
        pages=(5, 24),
        url="https://doi.org/10.1023/A:1018693118268",
        year=1999
)

Book("BrouwerNeumaier81",
     author=[("Brouwer", ("Andries", "E.")), ("Neumaier", ("Arnold", ))],
     title="Strongly regular graphs where mu equals two and lambda is large",
     series="Afdeling Zuivere Wiskunde [Department of Pure Mathematics]",
     pages=("i", 7),
     publisher="Stichting Mathematisch Centrum",
     address="Amsterdam",
     url="https://ir.cwi.nl/pub/6792/6792A.pdf",
     year=1981
)

InCollection("BrouwerVanLint84",
             author=[("Brouwer", ("Andries", "E.")),
                      ("van Lint", ("Jacobus", "Hendricus"))],
             title="Strongly regular graphs and partial geometries",
             booktitle="Enumeration and design (Waterloo, Ont., 1982)",
             pages=(85, 122),
             publisher="Academic Press",
             address="Toronto",
             url="https://ir.cwi.nl/pub/1817/1817A.pdf",
             year=1984
)

Article("CerzoSuzuki09",
        author=[("Cerzo", ("Diana", "R.")), ("Suzuki", ("Hiroshi", ))],
        title="Non-existence of imprimitive $Q$-polynomial schemes "
              "of exceptional type with $d = 4$",
        journal="European J. Combin.",
        fjournal="European Journal of Combinatorics",
        volume=30,
        number=3,
        pages=(674, 681),
        url="https://doi.org/10.1016/j.ejc.2008.07.014",
        year=2009
)

Article("Coolsaet95",
        author=[("Coolsaet", ("Kris", ))],
        title="Local structure of graphs with "
              r"$\lambda = \mu = 2$, $a_2 = 4$",
        journal="Combinatorica",
        fjournal="Combinatorica",
        volume=15,
        number=4,
        pages=(481, 487),
        url="https://doi.org/10.1007/BF01192521",
        year=1995
)

Article("Coolsaet05",
        author=[("Coolsaet", ("Kris", ))],
        title="A distance regular graph with intersection array "
              "(21, 16, 8; 1, 4, 14) does not exist",
        journal="European J. Combin.",
        fjournal="European Journal of Combinatorics",
        volume=26,
        number=5,
        pages=(709, 716),
        url="https://doi.org/10.1016/j.ejc.2004.04.005",
        year=2005
)

Article("CoolsaetJurišić08",
        author=[("Coolsaet", ("Kris", )), ("Jurišić", ("Aleksandar", ))],
        title="Using equality in the Krein conditions "
              "to prove nonexistence of certain distance-regular graphs",
        journal="J. Combin. Theory Ser. A",
        fjournal="Journal of Combinatorial Theory, Series A",
        volume=115,
        number=6,
        pages=(1086, 1095),
        url="https://doi.org/10.1016/j.jcta.2007.12.001",
        year=2008
)

Article("CJK08",
        author=[("Coolsaet", ("Kris", )), ("Jurišić", ("Aleksandar", )),
                 ("Koolen", ("Jack", ))],
        title="On triangle-free distance-regular graphs "
              "with an eigenvalue multiplicity equal to the valency",
        journal="European J. Combin.",
        fjournal="European Journal of Combinatorics",
        volume=29,
        number=5,
        pages=(1186, 1199),
        url="https://doi.org/10.1016/j.ejc.2007.06.010",
        year=2008
)

Article("vanDam95",
        author=[("van Dam", ("Edwin", "R."))],
        title="Regular graphs with four eigenvalues",
        journal="Linear Algebra Appl.",
        fjournal="Linear Algebra and its Applications",
        volume=(226, 228),
        pages=(139, 162),
        url="https://doi.org/10.1016/0024-3795(94)00346-F",
        year=1995
)

Article("DeBruyn01",
        author=[("De Bruyn", ("Bart", ))],
        title="Near hexagons with four points on a line",
        journal="Adv. Geom.",
        fjournal="Advances in Geometry",
        volume=1,
        number=3,
        pages=(211, 228),
        url="https://doi.org/10.1515/advg.2001.014",
        year=2001
)

Article("DeBruynVanhove15",
        author=[("De Bruyn", ("Bart", )), ("Vanhove", ("Frédéric", ))],
        title="On $Q$-polynomial regular near $2d$-gons",
        journal="Combinatorica",
        fjournal="Combinatorica",
        volume=35,
        number=2,
        pages=(181, 208),
        url="https://doi.org/10.1007/s00493-014-3039-x",
        year=2015
)

PhDThesis("Degraer07",
          author=[("Degraer", ("Jan", ))],
          title="Isomorph-free exhaustive generation algorithms "
                "for association schemes",
          school="Ghent University",
          year=2007
)

Article("Fon-Der-Flaass93a",
        author=[("Fon-Der-Flaass", ("Dmitrii", "Germanovich"))],
        title="A distance-regular graph with intersection array "
              "$(5, 4, 3, 3; 1, 1, 1, 2)$ does not exist",
        journal="J. Algebraic Combin.",
        fjournal="Journal of Algebraic Combinatorics",
        volume=2,
        number=1,
        pages=(49, 56),
        url="https://doi.org/10.1023/A:1022476614402",
        year=1993
)

Article("Fon-Der-Flaass93b",
        author=[("Fon-Der-Flaass", ("Dmitrii", "Germanovich"))],
        title="There exists no distance-regular graph "
              "with intersection array $(5, 4, 3; 1, 1, 2)$",
        journal="European J. Combin.",
        fjournal="European Journal of Combinatorics",
        volume=14,
        number=5,
        pages=(409, 412),
        url="https://doi.org/10.1006/eujc.1993.1045",
        year=1993
)

Article("Gavrilyuk11",
        author=[("Gavrilyuk", ("Alexander", "L."))],
        title="Distance-regular graphs with intersection arrays "
              r"$\{55, 36, 11; 1, 4, 45\}$ and $\{56, 36, 9; 1, 3, 48\}$ "
              "do not exist",
        journal="Dokl. Math.",
        fjournal="Doklady Mathematics",
        volume=84,
        number=1,
        pages=(444, 446),
        url="https://doi.org/10.1134/S1064562411040028",
        year=2011
)

Article("GavrilyukKoolen16",
        author=[("Gavrilyuk", ("Alexander", "L.")),
                 ("Koolen", ("Jack", "H."))],
        title="The Terwilliger polynomial of a $Q$-polynomial "
              "distance-regular graph and its application "
              "to pseudo-partition graphs",
        journal="Linear Algebra Appl.",
        fjournal="Linear Algebra and its Applications",
        volume=466,
        pages=(117, 140),
        url="https://doi.org/10.1016/j.laa.2014.09.048",
        year=2016
)

Unpublished("GavrilyukKoolen18",
            author=[("Gavrilyuk", ("Alexander", "L.")),
                    ("Koolen", ("Jack", "H."))],
            title="On a characterization of the Grassmann graphs",
            note="manuscript",
            url="https://arxiv.org/abs/1806.02652",
            year=2018
)

Article("GavrilyukKoolen19",
        author=[("Gavrilyuk", ("Alexander", "L.")),
                 ("Koolen", ("Jack", "H."))],
        title="A characterization of the graphs of bilinear "
              r"$(d \times d)$-forms over $\mathbb{F}_2$",
        journal="Combinatorica",
        fjournal="Combinatorica",
        volume=39,
        number=2,
        pages=(289, 321),
        url="https://doi.org/10.1007/s00493-017-3573-4",
        year=2019
)

Article("GavrilyukMakhnev05",
        author=[("Gavrilyuk", ("Alexander", "L.")),
                 ("Makhnev", ("Alexander", "Alexeevich"))],
        title="Krein graphs without triangles",
        journal="Dokl. Math.",
        fjournal="Doklady Mathematics",
        volume=72,
        number=1,
        pages=(591, 594),
        year=2005
)

Article("GavrilyukMakhnev12",
        author=[("Gavrilyuk", ("Alexander", "L.")),
                 ("Makhnev", ("Alexander", "Alexeevich"))],
        title="Distance-regular graphs with intersection arrays "
              r"$\{52, 35, 16; 1, 4, 28\}$ and $\{69, 48, 24; 1, 4, 46\}$ "
              "do not exist",
        journal="Des. Codes Cryptogr.",
        fjournal="Designs, Codes and Cryptography",
        volume=65,
        number=(1, 2),
        pages=(49, 54),
        url="https://doi.org/10.1007/s10623-012-9695-1",
        year=2012
)

Article("GavrilyukMakhnev13",
        author=[("Gavrilyuk", ("Alexander", "L.")),
                 ("Makhnev", ("Alexander", "Alexeevich"))],
        title="A distance-regular graph with intersection array "
              r"$\{45, 30, 7; 1, 2, 27\}$ does not exist",
        journal="Diskret. Mat.",
        fjournal="Diskretnaya Matematika",
        volume=25,
        number=2,
        pages=(13, 30),
        year=2013
)

Unpublished("KoolenGebremichel21",
            author=[("Koolen", ("Jack", "H.")), ("Gebremichel", ("Brhane", ))],
            title="There does not exist a strongly regular graph "
                  "with parameters $(1911,270,105,27)$",
            note="manuscript",
            url="https://arxiv.org/abs/2109.04000",
            year=2021
)

Article("GodsilHensel92",
        author=[("Godsil", ("Christopher", "D.")), ("Hensel", ("A.", "D."))],
        title="Distance regular covers of the complete graph",
        journal="J. Combin. Theory Ser. B",
        fjournal="Journal of Combinatorial Theory, Series B",
        volume=56,
        number=2,
        pages=(205, 238),
        url="https://doi.org/10.1016/0095-8956(92)90019-T",
        year=1992
)

Article("GodsilKoolen95",
        author=[("Godsil", ("Christopher", "D.")),
                 ("Koolen", ("Jacobus", "Hendricus"))],
        title="On the multiplicity of eigenvalues of distance-regular graphs",
        journal="Linear Algebra Appl.",
        fjournal="Linear Algebra and its Applications",
        volume=(226, 228),
        pages=(273, 275),
        url="https://doi.org/10.1016/0024-3795(95)00152-H",
        year=1995
)

Article("GKMP20",
        author=[("Guo", ("Ivan", )), ("Koolen", ("Jack", "H.")),
                 ("Markovsky", ("Greg", )), ("Park", ("Jongyook", ))],
        title="On the nonexistence of pseudo-generalized quadrangles",
        journal="European J. Combin.",
        fjournal="European Journal of Combinatorics",
        volume=89,
        pages=103128,
        url="https://doi.org/10.1016/j.ejc.2020.103128",
        year=2020
)

Article("GKP21",
        author=[("Greaves", ("Gary", "R.", "W.")),
                ("Koolen", ("Jack", "H.")),
                ("Park", ("Jongyook", ))],
        title="Augmenting the Delsarte bound: a forbidden interval for "
              "the order of maximal cliques in strongly regular graphs",
        journal="European J. Combin.",
        fjournal="European Journal of Combinatorics",
        volume=97,
        pages=103384,
        url="https://doi.org/10.1016/j.ejc.2021.103384",
        year=2021
)

Article("GSV20",
        author=[("Gavrilyuk", ("Alexander", "L.")), ("Suda", ("Sho", )),
                 ("Vidali", ("Janoš", ))],
        title="On tight $4$-designs in Hamming association schemes",
        journal="Combinatorica",
        fjournal="Combinatorica",
        volume=40,
        number=3,
        pages=(345, 362),
        url="https://doi.org/10.1007/s00493-019-4115-z",
        year=2020
)

Article("GVW21",
        author=[("Gavrilyuk", ("Alexander", "L.")),
                ("Vidali", ("Janoš", )),
                ("Williford", ("Jason", "S."))],
        title="On few-class $Q$-polynomial association schemes: "
              "feasible parameters and nonexistence results",
        journal="Ars Math. Contemp.",
        fjournal="Ars Mathematica Contemporanea",
        volume=20,
        number=1,
        pages=(103, 127),
        url="https://doi.org/10.26493/1855-3974.2101.b76",
        year=2021
)

InCollection("Haemers93",
             author=[("Haemers", ("Willem", "H."))],
             title="There exists no $(76, 21, 2, 7)$ strongly regular graph",
             booktitle="Finite geometry and combinatorics",
             series="London Mathematical Society Lecture Note Series",
             publisher="Cambridge Univ. Press",
             address="Cambridge",
             pages=(175, 176),
             url="https://doi.org/10.1017/CBO9780511526336.018",
             year=1993
)

Article("HPW15",
        author=[("Huang", ("Yu-pei", )), ("Pan", ("Yeh-jong", )),
                 ("Weng", ("Chih-wen", ))],
        title="Nonexistence of a class of distance-regular graphs",
        journal="Electron. J. Combin",
        fjournal="Electronic Journal of Combinatorics",
        volume=22,
        number=2,
        pages="2.37",
        url="http://www.combinatorics.org/ojs/index.php/eljc/article/"
            "view/v22i2p37",
        year=2015
)

Article("IvanovShpectorov90",
        author=[("Ivanov", ("Aleksandr", "Anatol'evich")),
                 ("Shpectorov", ("Sergey", "V."))],
        title="The $P$-geometry for $M_{23}$ has no nontrivial $2$-coverings",
        journal="European J. Combin.",
        fjournal="European Journal of Combinatorics",
        volume=11,
        number=4,
        pages=(373, 379),
        url="https://doi.org/10.1016/S0195-6698(13)80139-4",
        year=1990
)

Article("JurišićKoolen00",
        author=[("Jurišić", ("Aleksandar", )), ("Koolen", ("Jack", ))],
        title="Nonexistence of some antipodal distance-regular graphs "
              "of diameter four",
        journal="European J. Combin.",
        fjournal="European Journal of Combinatorics",
        volume=21,
        number=8,
        pages=(1039, 1046),
        year=2000
)

Article("JurišićKoolen11",
        author=[("Jurišić", ("Aleksandar", )), ("Koolen", ("Jack", ))],
        title=r"Classification of the family $\rm{AT4}(qs,q,q)$ "
              "of antipodal tight graphs",
        journal="J. Combin. Theory Ser. A",
        fjournal="Journal of Combinatorial Theory, Series A",
        volume=118,
        number=3,
        pages=(842, 852),
        year=2011
)

Article("JurišićVidali12",
        author=[("Jurišić", ("Aleksandar", )), ("Vidali", ("Janoš", ))],
        title="Extremal $1$-codes in distance-regular graphs of diameter $3$",
        journal="Des. Codes Cryptogr.",
        fjournal="Designs, Codes and Cryptography",
        volume=65,
        number=(1, 2),
        pages=(29, 47),
        url="https://doi.org/10.1007/s10623-012-9651-0",
        year=2012
)

Article("JurišićVidali17",
        author=[("Jurišić", ("Aleksandar", )), ("Vidali", ("Janoš", ))],
        title="Restrictions on classical distance-regular graphs",
        journal="J. Algebraic Combin.",
        fjournal="Journal of Algebraic Combinatorics",
        volume=46,
        pages=(571, 588),
        url="https://doi.org/10.1007/s10801-017-0765-3",
        year=2017
)

Article("JKT00",
        author=[("Jurišić", ("Aleksandar", )), ("Koolen", ("Jack", )),
                 ("Terwilliger", ("Paul", ))],
        title="Tight distance-regular graphs",
        journal="J. Algebraic Combin.",
        fjournal="Journal of Algebraic Combinatorics",
        volume=12,
        number=2,
        pages=(163, 197),
        url="https://doi.org/10.1023/A:1026544111089",
        year=2000
)

Article("KIPR19",
        author=[("Koolen", ("Jack", "H.")), ("Iqbal", ("Quaid", )),
                 ("Park", ("Jongyook", )), ("Ur Rehman", ("Masood", ))],
        title="There does not exist a distance-regular graph "
              r"with intersection array $\{80, 54, 12; 1, 6, 60\}$",
        journal="Graphs Combin.",
        fjournal="Graphs and Combinatorics",
        volume=35,
        pages=(1597, 1608),
        url="https://doi.org/10.1007/s00373-019-02095-2",
        year=2019
)

PhDThesis("Kodalen19",
          author=[("Kodalen", ("Brian", "G."))],
          title="Cometric association schemes",
          school="Worcester Polytechnic Institute",
          url="https://arxiv.org/abs/1905.06959",
          year=2019
)

Article("Koolen92",
        author=[("Koolen", ("Jacobus", "H."))],
        title="A new condition for distance-regular graphs",
        journal="European J. Combin.",
        fjournal="European Journal of Combinatorics",
        volume=13,
        number=1,
        pages=(63, 64),
        url="https://doi.org/10.1016/0195-6698(92)90068-B",
        year=1992
)

Article("KoolenPark10",
        author=[("Koolen", ("Jack", "H.")), ("Park", ("Jongyook", ))],
        title="Shilla distance-regular graphs",
        journal="European J. Combin.",
        fjournal="European Journal of Combinatorics",
        volume=31,
        number=8,
        pages=(2064, 2073),
        url="https://doi.org/10.1016/j.ejc.2010.05.012",
        year=2010
)

Article("Lambeck93",
        author=[("Lambeck", ("Ernst", ))],
        title="Some elementary inequalities for distance-regular graphs",
        journal="European J. Combin.",
        fjournal="European Journal of Combinatorics",
        volume=14,
        number=1,
        pages=(53, 54),
        url="https://doi.org/10.1006/eujc.1993.1008",
        year=1993
)

Article("LTS89",
        author=[("Lam", ("Clement", "Wing", "Hong")), ("Thiel", ("Larry", )),
                 ("Swiercz", ("S.", ))],
        title="The nonexistence of finite projective planes of order $10$",
        journal="Canad. J. Math.",
        fjournal="Canadian Journal of Mathematics",
        volume=41,
        number=6,
        pages=(1117, 1123),
        url="https://doi.org/10.4153/CJM-1989-049-4",
        year=1989
)

Article("Makhnev02",
        author=[("Makhnev", ("Alexander", "Alexeevich"))],
        title="On the nonexistence of strongly regular graphs "
              "with the parameters $(486, 165, 36, 66)$",
        journal="Ukrain. Mat. Zh.",
        fjournal="Ukraïns′kiĭ Matematichniĭ Zhurnal",
        volume=54,
        number=7,
        pages=(941, 949),
        url="https://doi.org/10.1023/A:1022066425998",
        year=2002
)

Article("Makhnev17",
        author=[("Makhnev", ("Alexander", "Alexeevich"))],
        title="The graph Kre$(4)$ does not exist",
        journal="Dokl. Math.",
        fjournal="Doklady Mathematics",
        volume=96,
        number=1,
        pages=(348, 350),
        url="https://doi.org/10.1134/S1064562417040123",
        year=2017
)

Article("MakhnevBelousov21",
        author=[("Makhnev", ("Alexander", "Alexeevich")),
                ("Belousov", ("Ivan", "Nikolaevich"))],
        title="Shilla graphs with $b = 5$ and $b = 6$",
        journal="Ural Math. J.",
        fjournal="Ural Mathematical Journal",
        volume=7,
        number=2,
        pages=(51, 58),
        url="https://doi.org/10.15826/umj.2021.2.004",
        year=2021
)

Article("MartinWilliford09",
        author=[("Martin", ("William", "J.")),
                 ("Williford", ("Jason", "S."))],
        title="There are finitely many $Q$-polynomial association schemes "
              "with given first multiplicity at least three",
        journal="European J. Combin.",
        fjournal="European Journal of Combinatorics",
        volume=30,
        number=3,
        pages=(698, 704),
        url="https://doi.org/10.1016/j.ejc.2008.07.009",
        year=2009
)

Article("Metsch95",
        author=[("Metsch", ("Klaus", ))],
        title="A characterization of Grassmann graphs",
        journal="European J. Combin.",
        fjournal="European Journal of Combinatorics",
        volume=16,
        number=6,
        pages=(639, 644),
        url="https://doi.org/10.1016/0195-6698(95)90045-4",
        year=1995
)

Article("Metsch99",
        author=[("Metsch", ("Klaus", ))],
        title="On a characterization of bilinear forms graphs",
        journal="European J. Combin.",
        fjournal="European Journal of Combinatorics",
        volume=20,
        number=4,
        pages=(293, 306),
        url="https://doi.org/10.1006/eujc.1998.0280",
        year=1999
)

Article("PanWeng09",
        author=[("Pan", ("Yeh-jong", )), ("Weng", ("Chih-wen", ))],
        title="A note on triangle-free distance-regular graphs "
              r"with $a_2 \ne 0$",
        journal="J. Combin. Theory Ser. B",
        fjournal="Journal of Combinatorial Theory, Series B",
        volume=99,
        number=1,
        pages=(266, 270),
        url="https://doi.org/10.1016/j.jctb.2008.07.005",
        year=2009
)

Book("PayneThas",
     author=[("Payne", ("Stanley", "E.")), ("Thas", ("Joseph", "A."))],
     title="Finite generalized quadrangles",
     edition="Second",
     series="EMS Series of Lectures in Mathematics",
     publisher="European Mathematical Society (EMS)",
     address="Zürich",
     year=2009,
     url="https://doi.org/10.4171/066",
     pages=("xii", 287)
)

Article("Soicher17",
        author=[("Soicher", ("Leonard", "H."))],
        title="The uniqueness of a distance-regular graph "
              r"with intersection array $\{32, 27, 8, 1; 1, 4, 27, 32\}$ "
              "and related results",
        journal="Des. Codes Cryptogr.",
        fjournal="Designs, Codes and Cryptography",
        volume=84,
        number=(1, 2),
        pages=(101, 108),
        url="https://doi.org/10.1007/s10623-016-0223-6",
        year=2017
)

Article("SumalrojWorawannotai16",
        author=[("Sumalroj", ("Supalak", )),
                 ("Worawannotai", ("Chalermpong", ))],
        title="The nonexistence of a distance-regular graph "
              r"with intersection array $\{22,16,5;1,2,20\}$",
        journal="Electron. J. Combin",
        fjournal="Electronic Journal of Combinatorics",
        volume=23,
        number=1,
        pages="1.32",
        url="http://www.combinatorics.org/ojs/index.php/eljc/article/"
            "view/v23i1p32",
        year=2016
)

Article("Urlep12",
        author=[("Urlep", ("Matjaž", ))],
        title="Triple intersection numbers of "
              "$Q$-polynomial distance-regular graphs",
        journal="European J. Combin.",
        fjournal="European Journal of Combinatorics",
        volume=33,
        number=6,
        pages=(1246, 1252),
        url="https://doi.org/10.1016/j.ejc.2012.02.005",
        year=2012
)

PhDThesis("Vidali13",
          author=[("Vidali", ("Janoš", ))],
          title="Codes in distance-regular graphs",
          school="University of Ljubljana",
          url="http://eprints.fri.uni-lj.si/2167/",
          year=2013
)

Article("Vidali18",
        author=[("Vidali", ("Janoš", ))],
        title="Using symbolic computation "
              "to prove nonexistence of distance-regular graphs",
        journal="Electron. J. Combin",
        fjournal="Electronic Journal of Combinatorics",
        volume=25,
        number=4,
        pages="P4.21",
        url="http://www.combinatorics.org/ojs/index.php/eljc/article/"
            "view/v25i4p21",
        year=2018
)

Article("Weng99",
        author=[("Weng", ("Chih-wen", ))],
        title="Classical distance-regular graphs of negative type",
        journal="J. Combin. Theory Ser. B",
        fjournal="Journal of Combinatorial Theory, Series B",
        volume=76,
        number=1,
        pages=(93, 116),
        url="https://doi.org/10.1006/jctb.1998.1892",
        year=1999
)

Article("WilbrinkBrouwer83",
        author=[("Wilbrink", ("Hendrikus", "Adrianus")),
                 ("Brouwer", ("Andries", "E."))],
        title="A $(57, 14, 1)$ strongly regular graph does not exist",
        journal="Nederl. Akad. Wetensch. Indag. Math.",
        fjournal="Koninklijke Nederlandse Akademie van Wetenschappen. "
                 "Indagationes Mathematicae",
        volume=45,
        number=1,
        pages=(117, 121),
        year=1983
)
