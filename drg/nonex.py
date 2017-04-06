# -*- coding: utf-8 -*-
from sage.symbolic.ring import SR

sporadic = {
    ((14, 12), (1, 4)): "WilbrinkBrouwer83",
    ((16, 12), (1, 6)): "BHMW89",
    ((21, 18), (1, 7)): "Haemers93",
    ((30, 21), (1, 14)): "BPR14",
    ((32, 21), (1, 16)): "AzarijaMarc15",
    ((38, 27), (1, 18)): "Degraer07",
    ((40, 27), (1, 20)): "AzarijaMarc16",
    ((57, 56), (1, 12)): "GavrilyukMakhnev05",
    ((5, 4, 3), (1, 1, 2)): "Fon-Der-Flaass93b",
    ((13, 10, 7), (1, 2, 7)): "Coolsaet95",
    ((21, 16, 8), (1, 4, 14)): "Coolsaet05",
    ((22, 16, 5), (1, 2, 20)): "SumalrojWorawannotai16",
    ((45, 30, 7), (1, 2, 27)): "GavrilyukMakhnev13",
    ((52, 35, 16), (1, 4, 28)): "GavrilyukMakhnev12",
    ((55, 36, 11), (1, 4, 45)): "Gavrilyuk11",
    ((56, 36, 9), (1, 3, 48)): "Gavrilyuk11",
    ((69, 48, 24), (1, 4, 46)): "GavrilyukMakhnev12",
    ((74, 54, 15), (1, 9, 60)): u"CoolsaetJurišić08",
    ((105, 102, 99), (1, 2, 35)): "DeBruynVanhove15",
    ((130, 96, 18), (1, 12, 117)): u"JurišićVidali17",
    ((135, 128, 16), (1, 16, 120)): "Vidali13",
    ((234, 165, 12), (1, 30, 198)): "Vidali16",
    ((4818, 4248, 192), (1, 72, 4672)): u"JurišićVidali17",
    ((5928, 5920, 5888), (1, 5, 741)): "DeBruynVanhove15",
    ((120939612, 120939520, 120933632), (1, 65, 1314561)):
        "DeBruynVanhove15",
    ((97571175, 97571080, 97569275), (1, 20, 1027065)):
        "DeBruynVanhove15",
    ((290116365, 290116260, 290100825), (1, 148, 2763013)):
        "DeBruynVanhove15",
    ((5, 4, 3, 3), (1, 1, 1, 2)): "Fon-Der-Flaass93a",
    ((10, 9, 1, 1), (1, 1, 9, 10)): ("BCN", "Prop. 11.4.5."),
    ((32, 27, 6, 1), (1, 6, 27, 32)): "Soicher15",
    ((32, 27, 9, 1), (1, 3, 27, 32)): "Soicher15",
    ((56, 45, 20, 1), (1, 4, 45, 56)): ("BCN94", "Thm. 11.4.6."),
    ((55, 54, 50, 35, 10), (1, 5, 20, 45, 55)): "Vidali13a",
    ((15, 14, 12, 6, 1, 1), (1, 1, 3, 12, 14, 15)): "IvanovShpectorov90"
}

r = SR.symbol("__r")
t = SR.symbol("__t")

families = {
    ((4*r**3 + 8*r**2 + 6*r + 1, 2*r*(r+1)*(2*r+1), 2*r**2 + 2*r + 1),
     (1, 2*r*(r+1), (2*r+1)*(2*r**2+2*r+1))): (r >= 1,
                                               u"CoolsaetJurišić08"),
    (((2*r**2 - 1)*(2*r+1), 4*r*(r**2-1), 2*r**2),
     (1, 2*(r**2-1), r*(4*r**2-2))): (r >= 2, u"JurišićVidali12"),
    ((2*r**2*(2*r+1), (2*r-1)*(2*r**2+r+1), 2*r**2),
     (1, 2*r**2, r*(4*r**2-1))): (r >= 2, u"JurišićVidali12"),
    (((2*r+1)*(4*r+1)*(4*t-1), 8*r*(4*r*t-r+2*t), (r+t)*(4*r+1)),
     (1, (r+t)*(4*r+1), 4*r*(2*r+1)*(4*t-1))): ([r >= 1, t >= 1], "Vidali13"),
    (((r+1)*(r**3-1), r*(r-1)*(r**2+r-1), r**2-1),
     (1, r*(r+1), (r**2-1)*(r**2+r-1))): (r >= 3, "Urlep12"),
    ((r**2*(r*t+t+1), (r**2-1)*(r*t+1), r*(r-1)*(t+1), 1),
     (1, r*(t+1), (r**2-1)*(r*t+1), r**2*(r*t+t+1))):
         ([r >= 3, (r != 3, [t != 1, t != 3]), (r != 4, t != 2)],
          u"JurišićKoolen11"),
    ((2*r**2+r, 2*r**2+r-1, r**2, r, 1), (1, r, r**2, 2*r**2+r-1, 2*r**2+r)):
        (r >= 2, "CJK08")
}

classicalFamilies = {
    (t, -r, -r/(r-1), r + r**2 * ((-r)**(t-1) - 1) / (r**2-1)):
        ([r >= 2, t >= 4], "DeBruynVanhove15")
}

def checkConditions(cond, sol):
    """
    Check whether the given conditions hold for the given values of variables.
    """
    if isinstance(cond, list):
        return all(checkConditions(cnd, sol) for cnd in cond)
    elif isinstance(cond, tuple):
        return any(checkConditions(cnd, sol) for cnd in cond)
    else:
        return cond.subs(sol)
