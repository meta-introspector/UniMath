(* Section WithUniMath . *)
Require Export UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.CategoryTheory.Inductives.Lists .
Require Import UniMath.Algebra.IteratedBinaryOperations.
Require Import Datatypes.
(* Local Notation "[]" := Lists.nil (at level 0, format "[]"). *)
(* Local Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..). *)
(* Local Infix "::" := cons. *)


(* Definition Foundations := Type. *)
(* Definition UniMath := Type. *)



(*TODO:infix fun DirPath lst*)


Inductive myModules : Type :=
| Init
| Preamble
| Foundations
| UniMath .

Inductive myTerms : Type :=
| Id (a :myModules).

Inductive mylist : Set :=
| mynil
| mycons (hd : myTerms) (tl : mylist ).

Inductive mylist2 : Set :=
| mynil2
| mycons2 (hd : myModules) (tl : mylist2 ).

Inductive myFuncts : Set :=
| v3 (a : myFuncts)( b : myFuncts)(c : myFuncts)
| v2 (a : myFuncts)( b : myFuncts)
| v1 (a : myFuncts)
| ImportAll : myFuncts
| line_nb_last (a : Preamble.nat)
| bol_pos_last (a : Preamble.nat)
| bp (a : Preamble.nat)
| ep (a : Preamble.nat)
| line_nb (a : Preamble.nat)
| bol_pos (a : Preamble.nat)
| DirPath  (a : mylist)
| CSort  (a : myFuncts)
| UAnonymous  (a : myFuncts)
| rigid  (a : bool)
| file (a : mylist2)
| Name (a : myFuncts)
| InFile (a : myFuncts)(b : myFuncts)
| dirpath : myFuncts
| fname (a : myFuncts)(b : myFuncts)(c : myFuncts)(d : myFuncts)(e : myFuncts)(f : myFuncts)(g : myFuncts)
| Ser_Qualid (a : myFuncts)(a : myTerms)
| Id2 (a :Type)
| control (a : myFuncts)(b : myFuncts)
| attrs :  myFuncts
| expr  (a : myFuncts)
| VernacSynterp(a : myFuncts)
| VernacRequire (a : myFuncts)(b : myFuncts)
| DefineBody (a : myFuncts)
| DefineBody2 (a : myFuncts)(b : myFuncts)
| VernacSynPure(a : myFuncts)
| VernacDefinition (pre : myFuncts)(name : myFuncts)(def : myFuncts)
| AdExport : myFuncts
| NoDischarge_Definition : myFuncts
| loc (a : myFuncts)


.
(* Notation  "12" := O : nat_scope. *)


(* Notation  "1002" := (S 1) : nat_scope. *)
(* Notation  "1003" := (S 1) : nat_scope. *)
(* Notation  "101" := (S 1) : nat_scope. *)
(* Notation  "1013" := (S 1) : nat_scope. *)
(* Notation  "1016" := (S 1) : nat_scope. *)
(* Notation  "1025" := (S 1) : nat_scope. *)
(* Notation  "1026" := (S 1) : nat_scope. *)
(* Notation  "103" := (S 1) : nat_scope. *)
(* Notation  "1036" := (S 1) : nat_scope. *)
(* Notation  "1039" := (S 1) : nat_scope. *)
(* Notation  "104" := (S 1) : nat_scope. *)
(* Notation  "1048" := (S 1) : nat_scope. *)
(* Notation  "105" := (S 1) : nat_scope. *)
(* Notation  "1050" := (S 1) : nat_scope. *)
(* Notation  "1059" := (S 1) : nat_scope. *)
(* Notation  "106" := (S 1) : nat_scope. *)
(* Notation  "1062" := (S 1) : nat_scope. *)
(* Notation  "1066" := (S 1) : nat_scope. *)
(* Notation  "1069" := (S 1) : nat_scope. *)
(* Notation  "107" := (S 1) : nat_scope. *)
(* Notation  "1070" := (S 1) : nat_scope. *)
(* Notation  "108" := (S 1) : nat_scope. *)
(* Notation  "11" := (S 1) : nat_scope. *)
(* Notation  "110" := (S 1) : nat_scope. *)
(* Notation  "111" := (S 1) : nat_scope. *)
(* Notation  "112" := (S 1) : nat_scope. *)
(* Notation  "1127" := (S 1) : nat_scope. *)
(* Notation  "113" := (S 1) : nat_scope. *)
(* Notation  "1136" := (S 1) : nat_scope. *)
(* Notation  "1139" := (S 1) : nat_scope. *)
(* Notation  "114" := (S 1) : nat_scope. *)
(* Notation  "1143" := (S 1) : nat_scope. *)
(* Notation  "1146" := (S 1) : nat_scope. *)
(* Notation  "1147" := (S 1) : nat_scope. *)
(* Notation  "115" := (S 1) : nat_scope. *)
(* Notation  "116" := (S 1) : nat_scope. *)
(* Notation  "117" := (S 1) : nat_scope. *)
(* Notation  "118" := (S 1) : nat_scope. *)
(* Notation  "119" := (S 1) : nat_scope. *)

(* Notation  "120" := (S 1) : nat_scope. *)
(* Notation  "1205" := (S 1) : nat_scope. *)
(* Notation  "121" := (S 1) : nat_scope. *)
(* Notation  "1214" := (S 1) : nat_scope. *)
(* Notation  "122" := (S 1) : nat_scope. *)
(* Notation  "1223" := (S 1) : nat_scope. *)
(* Notation  "1228" := (S 1) : nat_scope. *)
(* Notation  "123" := (S 1) : nat_scope. *)
(* Notation  "1234" := (S 1) : nat_scope. *)
(* Notation  "1235" := (S 1) : nat_scope. *)
(* Notation  "1236" := (S 1) : nat_scope. *)
(* Notation  "1237" := (S 1) : nat_scope. *)
(* Notation  "1238" := (S 1) : nat_scope. *)
(* Notation  "124" := (S 1) : nat_scope. *)
(* Notation  "1240" := (S 1) : nat_scope. *)
(* Notation  "125" := (S 1) : nat_scope. *)
(* Notation  "126" := (S 1) : nat_scope. *)
(* Notation  "127" := (S 1) : nat_scope. *)
(* Notation  "128" := (S 1) : nat_scope. *)
(* Notation  "129" := (S 1) : nat_scope. *)
(* Notation  "13" := (S 1) : nat_scope. *)
(* Notation  "130" := (S 1) : nat_scope. *)
(* Notation  "131" := (S 1) : nat_scope. *)
(* Notation  "132" := (S 1) : nat_scope. *)
(* Notation  "133" := (S 1) : nat_scope. *)
(* Notation  "134" := (S 1) : nat_scope. *)
(* Notation  "135" := (S 1) : nat_scope. *)
(* Notation  "136" := (S 1) : nat_scope. *)
(* Notation  "1382" := (S 1) : nat_scope. *)
(* Notation  "1392" := (S 1) : nat_scope. *)
(* Notation  "1395" := (S 1) : nat_scope. *)
(* Notation  "1398" := (S 1) : nat_scope. *)
(* Notation  "14" := (S 1) : nat_scope. *)
(* Notation  "140" := (S 1) : nat_scope. *)
(* Notation  "1400" := (S 1) : nat_scope. *)
(* Notation  "1404" := (S 1) : nat_scope. *)
(* Notation  "1408" := (S 1) : nat_scope. *)
(* Notation  "1409" := (S 1) : nat_scope. *)
(* Notation  "141" := (S 1) : nat_scope. *)
(* Notation  "1412" := (S 1) : nat_scope. *)
(* Notation  "1415" := (S 1) : nat_scope. *)
(* Notation  "1416" := (S 1) : nat_scope. *)
(* Notation  "142" := (S 1) : nat_scope. *)
(* Notation  "1420" := (S 1) : nat_scope. *)
(* Notation  "1421" := (S 1) : nat_scope. *)
(* Notation  "1424" := (S 1) : nat_scope. *)
(* Notation  "1427" := (S 1) : nat_scope. *)
(* Notation  "143" := (S 1) : nat_scope. *)
(* Notation  "1431" := (S 1) : nat_scope. *)
(* Notation  "1434" := (S 1) : nat_scope. *)
(* Notation  "1435" := (S 1) : nat_scope. *)
(* Notation  "1437" := (S 1) : nat_scope. *)
(* Notation  "144" := (S 1) : nat_scope. *)
(* Notation  "1448" := (S 1) : nat_scope. *)
(* Notation  "1452" := (S 1) : nat_scope. *)
(* Notation  "1456" := (S 1) : nat_scope. *)
(* Notation  "1457" := (S 1) : nat_scope. *)
(* Notation  "1458" := (S 1) : nat_scope. *)
(* Notation  "1460" := (S 1) : nat_scope. *)
(* Notation  "1484" := (S 1) : nat_scope. *)
(* Notation  "1485" := (S 1) : nat_scope. *)
(* Notation  "15" := (S 1) : nat_scope. *)
(* Notation  "1518" := (S 1) : nat_scope. *)
(* Notation  "1519" := (S 1) : nat_scope. *)
(* Notation  "1545" := (S 1) : nat_scope. *)
(* Notation  "1548" := (S 1) : nat_scope. *)
(* Notation  "1549" := (S 1) : nat_scope. *)
(* Notation  "1550" := (S 1) : nat_scope. *)
(* Notation  "1560" := (S 1) : nat_scope. *)
(* Notation  "1561" := (S 1) : nat_scope. *)
(* Notation  "1562" := (S 1) : nat_scope. *)
(* Notation  "1567" := (S 1) : nat_scope. *)
(* Notation  "1568" := (S 1) : nat_scope. *)
(* Notation  "1569" := (S 1) : nat_scope. *)
(* Notation  "1590" := (S 1) : nat_scope. *)
(* Notation  "1592" := (S 1) : nat_scope. *)
(* Notation  "16" := (S 1) : nat_scope. *)
(* Notation  "1601" := (S 1) : nat_scope. *)
(* Notation  "1604" := (S 1) : nat_scope. *)
(* Notation  "1605" := (S 1) : nat_scope. *)
(* Notation  "1606" := (S 1) : nat_scope. *)
(* Notation  "1607" := (S 1) : nat_scope. *)
(* Notation  "1608" := (S 1) : nat_scope. *)
(* Notation  "1612" := (S 1) : nat_scope. *)
(* Notation  "1614" := (S 1) : nat_scope. *)
(* Notation  "1620" := (S 1) : nat_scope. *)
(* Notation  "1621" := (S 1) : nat_scope. *)
(* Notation  "1627" := (S 1) : nat_scope. *)
(* Notation  "1631" := (S 1) : nat_scope. *)
(* Notation  "1632" := (S 1) : nat_scope. *)
(* Notation  "1636" := (S 1) : nat_scope. *)
(* Notation  "1637" := (S 1) : nat_scope. *)
(* Notation  "1638" := (S 1) : nat_scope. *)
(* Notation  "1642" := (S 1) : nat_scope. *)
(* Notation  "1643" := (S 1) : nat_scope. *)
(* Notation  "1644" := (S 1) : nat_scope. *)
(* Notation  "1645" := (S 1) : nat_scope. *)
(* Notation  "1649" := (S 1) : nat_scope. *)
(* Notation  "1650" := (S 1) : nat_scope. *)
(* Notation  "1652" := (S 1) : nat_scope. *)
(* Notation  "1653" := (S 1) : nat_scope. *)
(* Notation  "1656" := (S 1) : nat_scope. *)
(* Notation  "1657" := (S 1) : nat_scope. *)
(* Notation  "1658" := (S 1) : nat_scope. *)
(* Notation  "1659" := (S 1) : nat_scope. *)
(* Notation  "1664" := (S 1) : nat_scope. *)
(* Notation  "1665" := (S 1) : nat_scope. *)
(* Notation  "1671" := (S 1) : nat_scope. *)
(* Notation  "1678" := (S 1) : nat_scope. *)
(* Notation  "1683" := (S 1) : nat_scope. *)
(* Notation  "1686" := (S 1) : nat_scope. *)
(* Notation  "1687" := (S 1) : nat_scope. *)
(* Notation  "1688" := (S 1) : nat_scope. *)
(* Notation  "1689" := (S 1) : nat_scope. *)
(* Notation  "1690" := (S 1) : nat_scope. *)
(* Notation  "17" := (S 1) : nat_scope. *)
(* Notation  "1704" := (S 1) : nat_scope. *)
(* Notation  "1706" := (S 1) : nat_scope. *)
(* Notation  "1715" := (S 1) : nat_scope. *)
(* Notation  "1718" := (S 1) : nat_scope. *)
(* Notation  "1719" := (S 1) : nat_scope. *)
(* Notation  "1720" := (S 1) : nat_scope. *)
(* Notation  "1721" := (S 1) : nat_scope. *)
(* Notation  "1722" := (S 1) : nat_scope. *)
(* Notation  "1726" := (S 1) : nat_scope. *)
(* Notation  "1728" := (S 1) : nat_scope. *)
(* Notation  "1734" := (S 1) : nat_scope. *)
(* Notation  "1735" := (S 1) : nat_scope. *)
(* Notation  "1737" := (S 1) : nat_scope. *)
(* Notation  "1738" := (S 1) : nat_scope. *)
(* Notation  "1744" := (S 1) : nat_scope. *)
(* Notation  "1748" := (S 1) : nat_scope. *)
(* Notation  "1749" := (S 1) : nat_scope. *)
(* Notation  "1750" := (S 1) : nat_scope. *)
(* Notation  "1751" := (S 1) : nat_scope. *)
(* Notation  "1753" := (S 1) : nat_scope. *)
(* Notation  "1754" := (S 1) : nat_scope. *)
(* Notation  "1755" := (S 1) : nat_scope. *)
(* Notation  "1756" := (S 1) : nat_scope. *)
(* Notation  "1760" := (S 1) : nat_scope. *)
(* Notation  "1761" := (S 1) : nat_scope. *)
(* Notation  "1764" := (S 1) : nat_scope. *)
(* Notation  "1765" := (S 1) : nat_scope. *)
(* Notation  "1766" := (S 1) : nat_scope. *)
(* Notation  "1770" := (S 1) : nat_scope. *)
(* Notation  "1771" := (S 1) : nat_scope. *)
(* Notation  "1773" := (S 1) : nat_scope. *)
(* Notation  "1774" := (S 1) : nat_scope. *)
(* Notation  "1778" := (S 1) : nat_scope. *)
(* Notation  "1779" := (S 1) : nat_scope. *)
(* Notation  "178" := (S 1) : nat_scope. *)
(* Notation  "1780" := (S 1) : nat_scope. *)
(* Notation  "1785" := (S 1) : nat_scope. *)
(* Notation  "1786" := (S 1) : nat_scope. *)
(* Notation  "179" := (S 1) : nat_scope. *)
(* Notation  "1792" := (S 1) : nat_scope. *)
(* Notation  "1799" := (S 1) : nat_scope. *)
(* Notation  "18" := (S 1) : nat_scope. *)
(* Notation  "1804" := (S 1) : nat_scope. *)
(* Notation  "1807" := (S 1) : nat_scope. *)
(* Notation  "1808" := (S 1) : nat_scope. *)
(* Notation  "1809" := (S 1) : nat_scope. *)
(* Notation  "181" := (S 1) : nat_scope. *)
(* Notation  "1810" := (S 1) : nat_scope. *)
(* Notation  "1811" := (S 1) : nat_scope. *)
(* Notation  "1825" := (S 1) : nat_scope. *)
(* Notation  "183" := (S 1) : nat_scope. *)
(* Notation  "184" := (S 1) : nat_scope. *)
(* Notation  "185" := (S 1) : nat_scope. *)
(* Notation  "187" := (S 1) : nat_scope. *)
(* Notation  "188" := (S 1) : nat_scope. *)
(* Notation  "1882" := (S 1) : nat_scope. *)
(* Notation  "1893" := (S 1) : nat_scope. *)
(* Notation  "1896" := (S 1) : nat_scope. *)
(* Notation  "1899" := (S 1) : nat_scope. *)
(* Notation  "19" := (S 1) : nat_scope. *)
(* Notation  "1902" := (S 1) : nat_scope. *)
(* Notation  "1906" := (S 1) : nat_scope. *)
(* Notation  "1909" := (S 1) : nat_scope. *)
(* Notation  "1913" := (S 1) : nat_scope. *)
(* Notation  "1916" := (S 1) : nat_scope. *)
(* Notation  "1917" := (S 1) : nat_scope. *)
(* Notation  "1918" := (S 1) : nat_scope. *)
(* Notation  "1924" := (S 1) : nat_scope. *)
(* Notation  "1925" := (S 1) : nat_scope. *)
(* Notation  "1927" := (S 1) : nat_scope. *)
(* Notation  "1934" := (S 1) : nat_scope. *)
(* Notation  "1935" := (S 1) : nat_scope. *)
(* Notation  "1936" := (S 1) : nat_scope. *)
(* Notation  "1937" := (S 1) : nat_scope. *)
(* Notation  "1938" := (S 1) : nat_scope. *)
(* Notation  "1939" := (S 1) : nat_scope. *)
(* Notation  "1941" := (S 1) : nat_scope. *)
(* Notation  "1951" := (S 1) : nat_scope. *)
(* Notation  "1952" := (S 1) : nat_scope. *)
(* Notation  "1956" := (S 1) : nat_scope. *)
(* Notation  "1958" := (S 1) : nat_scope. *)
(* Notation  "1959" := (S 1) : nat_scope. *)
(* Notation  "1960" := (S 1) : nat_scope. *)
(* Notation  "1962" := (S 1) : nat_scope. *)
(* Notation  "1963" := (S 1) : nat_scope. *)
(* Notation  "1964" := (S 1) : nat_scope. *)
(* Notation  "1965" := (S 1) : nat_scope. *)
(* Notation  "1967" := (S 1) : nat_scope. *)
(* Notation  "1968" := (S 1) : nat_scope. *)
(* Notation  "1969" := (S 1) : nat_scope. *)
(* Notation  "1975" := (S 1) : nat_scope. *)
(* Notation  "1976" := (S 1) : nat_scope. *)
(* Notation  "1977" := (S 1) : nat_scope. *)
(* Notation  "1978" := (S 1) : nat_scope. *)
(* Notation  "1980" := (S 1) : nat_scope. *)
(* Notation  "1981" := (S 1) : nat_scope. *)
(* Notation  "1982" := (S 1) : nat_scope. *)
(* Notation  "1989" := (S 1) : nat_scope. *)
(* Notation  "1991" := (S 1) : nat_scope. *)
(* Notation  "1994" := (S 1) : nat_scope. *)
(* Notation  "1995" := (S 1) : nat_scope. *)
(* Notation  "1996" := (S 1) : nat_scope. *)
(* Notation  "1997" := (S 1) : nat_scope. *)
(* Notation  "1998" := (S 1) : nat_scope. *)
(* Notation  "2" := (S 1) : nat_scope. *)
(* Notation  "20" := (S 1) : nat_scope. *)
(* Notation  "200" := (S 1) : nat_scope. *)
(* Notation  "2006" := (S 1) : nat_scope. *)
(* Notation  "2008" := (S 1) : nat_scope. *)
(* Notation  "2017" := (S 1) : nat_scope. *)
(* Notation  "2024" := (S 1) : nat_scope. *)
(* Notation  "2029" := (S 1) : nat_scope. *)
(* Notation  "2032" := (S 1) : nat_scope. *)
(* Notation  "2033" := (S 1) : nat_scope. *)
(* Notation  "2034" := (S 1) : nat_scope. *)
(* Notation  "2035" := (S 1) : nat_scope. *)
(* Notation  "2036" := (S 1) : nat_scope. *)
(* Notation  "2050" := (S 1) : nat_scope. *)
(* Notation  "2052" := (S 1) : nat_scope. *)
(* Notation  "2061" := (S 1) : nat_scope. *)
(* Notation  "2064" := (S 1) : nat_scope. *)
(* Notation  "2065" := (S 1) : nat_scope. *)
(* Notation  "2066" := (S 1) : nat_scope. *)
(* Notation  "2067" := (S 1) : nat_scope. *)
(* Notation  "2068" := (S 1) : nat_scope. *)
(* Notation  "2072" := (S 1) : nat_scope. *)
(* Notation  "2074" := (S 1) : nat_scope. *)
(* Notation  "2080" := (S 1) : nat_scope. *)
(* Notation  "2081" := (S 1) : nat_scope. *)
(* Notation  "2083" := (S 1) : nat_scope. *)
(* Notation  "2084" := (S 1) : nat_scope. *)
(* Notation  "2090" := (S 1) : nat_scope. *)
(* Notation  "2096" := (S 1) : nat_scope. *)
(* Notation  "2097" := (S 1) : nat_scope. *)
(* Notation  "2099" := (S 1) : nat_scope. *)
(* Notation  "21" := (S 1) : nat_scope. *)
(* Notation  "2100" := (S 1) : nat_scope. *)
(* Notation  "2104" := (S 1) : nat_scope. *)
(* Notation  "2105" := (S 1) : nat_scope. *)
(* Notation  "2106" := (S 1) : nat_scope. *)
(* Notation  "2112" := (S 1) : nat_scope. *)
(* Notation  "2113" := (S 1) : nat_scope. *)
(* Notation  "2114" := (S 1) : nat_scope. *)
(* Notation  "2116" := (S 1) : nat_scope. *)
(* Notation  "2118" := (S 1) : nat_scope. *)
(* Notation  "2119" := (S 1) : nat_scope. *)
(* Notation  "2123" := (S 1) : nat_scope. *)
(* Notation  "2124" := (S 1) : nat_scope. *)
(* Notation  "2125" := (S 1) : nat_scope. *)
(* Notation  "2131" := (S 1) : nat_scope. *)
(* Notation  "2132" := (S 1) : nat_scope. *)
(* Notation  "2133" := (S 1) : nat_scope. *)
(* Notation  "2135" := (S 1) : nat_scope. *)
(* Notation  "2137" := (S 1) : nat_scope. *)
(* Notation  "2138" := (S 1) : nat_scope. *)
(* Notation  "2139" := (S 1) : nat_scope. *)
(* Notation  "2141" := (S 1) : nat_scope. *)
(* Notation  "2145" := (S 1) : nat_scope. *)
(* Notation  "2146" := (S 1) : nat_scope. *)
(* Notation  "2148" := (S 1) : nat_scope. *)
(* Notation  "2151" := (S 1) : nat_scope. *)
(* Notation  "2152" := (S 1) : nat_scope. *)
(* Notation  "2154" := (S 1) : nat_scope. *)
(* Notation  "2155" := (S 1) : nat_scope. *)
(* Notation  "2157" := (S 1) : nat_scope. *)
(* Notation  "2158" := (S 1) : nat_scope. *)
(* Notation  "2159" := (S 1) : nat_scope. *)
(* Notation  "2164" := (S 1) : nat_scope. *)
(* Notation  "2165" := (S 1) : nat_scope. *)
(* Notation  "2167" := (S 1) : nat_scope. *)
(* Notation  "2176" := (S 1) : nat_scope. *)
(* Notation  "2179" := (S 1) : nat_scope. *)
(* Notation  "2180" := (S 1) : nat_scope. *)
(* Notation  "2181" := (S 1) : nat_scope. *)
(* Notation  "2182" := (S 1) : nat_scope. *)
(* Notation  "2183" := (S 1) : nat_scope. *)
(* Notation  "2187" := (S 1) : nat_scope. *)
(* Notation  "2189" := (S 1) : nat_scope. *)
(* Notation  "2195" := (S 1) : nat_scope. *)
(* Notation  "2196" := (S 1) : nat_scope. *)
(* Notation  "2198" := (S 1) : nat_scope. *)
(* Notation  "2199" := (S 1) : nat_scope. *)
(* Notation  "22" := (S 1) : nat_scope. *)
(* Notation  "2205" := (S 1) : nat_scope. *)
(* Notation  "2211" := (S 1) : nat_scope. *)
(* Notation  "2212" := (S 1) : nat_scope. *)
(* Notation  "2214" := (S 1) : nat_scope. *)
(* Notation  "2215" := (S 1) : nat_scope. *)
(* Notation  "2219" := (S 1) : nat_scope. *)
(* Notation  "2220" := (S 1) : nat_scope. *)
(* Notation  "2221" := (S 1) : nat_scope. *)
(* Notation  "2227" := (S 1) : nat_scope. *)
(* Notation  "2228" := (S 1) : nat_scope. *)
(* Notation  "2229" := (S 1) : nat_scope. *)
(* Notation  "2231" := (S 1) : nat_scope. *)
(* Notation  "2233" := (S 1) : nat_scope. *)
(* Notation  "2234" := (S 1) : nat_scope. *)
(* Notation  "2238" := (S 1) : nat_scope. *)
(* Notation  "2239" := (S 1) : nat_scope. *)
(* Notation  "2240" := (S 1) : nat_scope. *)
(* Notation  "2246" := (S 1) : nat_scope. *)
(* Notation  "2247" := (S 1) : nat_scope. *)
(* Notation  "2248" := (S 1) : nat_scope. *)
(* Notation  "2250" := (S 1) : nat_scope. *)
(* Notation  "2252" := (S 1) : nat_scope. *)
(* Notation  "2253" := (S 1) : nat_scope. *)
(* Notation  "2254" := (S 1) : nat_scope. *)
(* Notation  "2256" := (S 1) : nat_scope. *)
(* Notation  "2260" := (S 1) : nat_scope. *)
(* Notation  "2261" := (S 1) : nat_scope. *)
(* Notation  "2263" := (S 1) : nat_scope. *)
(* Notation  "2266" := (S 1) : nat_scope. *)
(* Notation  "2267" := (S 1) : nat_scope. *)
(* Notation  "2269" := (S 1) : nat_scope. *)
(* Notation  "2270" := (S 1) : nat_scope. *)
(* Notation  "2272" := (S 1) : nat_scope. *)
(* Notation  "2273" := (S 1) : nat_scope. *)
(* Notation  "2274" := (S 1) : nat_scope. *)
(* Notation  "2279" := (S 1) : nat_scope. *)
(* Notation  "2280" := (S 1) : nat_scope. *)
(* Notation  "2282" := (S 1) : nat_scope. *)
(* Notation  "2292" := (S 1) : nat_scope. *)
(* Notation  "2295" := (S 1) : nat_scope. *)
(* Notation  "23" := (S 1) : nat_scope. *)
(* Notation  "2300" := (S 1) : nat_scope. *)
(* Notation  "2301" := (S 1) : nat_scope. *)
(* Notation  "2315" := (S 1) : nat_scope. *)
(* Notation  "2316" := (S 1) : nat_scope. *)
(* Notation  "2326" := (S 1) : nat_scope. *)
(* Notation  "2329" := (S 1) : nat_scope. *)
(* Notation  "2334" := (S 1) : nat_scope. *)
(* Notation  "2335" := (S 1) : nat_scope. *)
(* Notation  "2336" := (S 1) : nat_scope. *)
(* Notation  "2337" := (S 1) : nat_scope. *)
(* Notation  "2351" := (S 1) : nat_scope. *)
(* Notation  "2352" := (S 1) : nat_scope. *)
(* Notation  "2362" := (S 1) : nat_scope. *)
(* Notation  "2365" := (S 1) : nat_scope. *)
(* Notation  "2370" := (S 1) : nat_scope. *)
(* Notation  "2371" := (S 1) : nat_scope. *)
(* Notation  "2372" := (S 1) : nat_scope. *)
(* Notation  "2373" := (S 1) : nat_scope. *)
(* Notation  "2387" := (S 1) : nat_scope. *)
(* Notation  "2388" := (S 1) : nat_scope. *)
(* Notation  "2398" := (S 1) : nat_scope. *)
(* Notation  "24" := (S 1) : nat_scope. *)
(* Notation  "2401" := (S 1) : nat_scope. *)
(* Notation  "2406" := (S 1) : nat_scope. *)
(* Notation  "2407" := (S 1) : nat_scope. *)
(* Notation  "2408" := (S 1) : nat_scope. *)
(* Notation  "2409" := (S 1) : nat_scope. *)
(* Notation  "2423" := (S 1) : nat_scope. *)
(* Notation  "2424" := (S 1) : nat_scope. *)
(* Notation  "2434" := (S 1) : nat_scope. *)
(* Notation  "2437" := (S 1) : nat_scope. *)
(* Notation  "2442" := (S 1) : nat_scope. *)
(* Notation  "2443" := (S 1) : nat_scope. *)
(* Notation  "2444" := (S 1) : nat_scope. *)
(* Notation  "2445" := (S 1) : nat_scope. *)
(* Notation  "2459" := (S 1) : nat_scope. *)
(* Notation  "2460" := (S 1) : nat_scope. *)
(* Notation  "2470" := (S 1) : nat_scope. *)
(* Notation  "2473" := (S 1) : nat_scope. *)
(* Notation  "2478" := (S 1) : nat_scope. *)
(* Notation  "2479" := (S 1) : nat_scope. *)
(* Notation  "2480" := (S 1) : nat_scope. *)
(* Notation  "2481" := (S 1) : nat_scope. *)
(* Notation  "2495" := (S 1) : nat_scope. *)
(* Notation  "2496" := (S 1) : nat_scope. *)
(* Notation  "2506" := (S 1) : nat_scope. *)
(* Notation  "2509" := (S 1) : nat_scope. *)
(* Notation  "2514" := (S 1) : nat_scope. *)
(* Notation  "2515" := (S 1) : nat_scope. *)
(* Notation  "2516" := (S 1) : nat_scope. *)
(* Notation  "2517" := (S 1) : nat_scope. *)
(* Notation  "2531" := (S 1) : nat_scope. *)
(* Notation  "2532" := (S 1) : nat_scope. *)
(* Notation  "2542" := (S 1) : nat_scope. *)
(* Notation  "2545" := (S 1) : nat_scope. *)
(* Notation  "2550" := (S 1) : nat_scope. *)
(* Notation  "2551" := (S 1) : nat_scope. *)
(* Notation  "2552" := (S 1) : nat_scope. *)
(* Notation  "2553" := (S 1) : nat_scope. *)
(* Notation  "2567" := (S 1) : nat_scope. *)
(* Notation  "2568" := (S 1) : nat_scope. *)
(* Notation  "2578" := (S 1) : nat_scope. *)
(* Notation  "2581" := (S 1) : nat_scope. *)
(* Notation  "2586" := (S 1) : nat_scope. *)
(* Notation  "2587" := (S 1) : nat_scope. *)
(* Notation  "2588" := (S 1) : nat_scope. *)
(* Notation  "2589" := (S 1) : nat_scope. *)
(* Notation  "2603" := (S 1) : nat_scope. *)
(* Notation  "2604" := (S 1) : nat_scope. *)
(* Notation  "2614" := (S 1) : nat_scope. *)
(* Notation  "2617" := (S 1) : nat_scope. *)
(* Notation  "2622" := (S 1) : nat_scope. *)
(* Notation  "2623" := (S 1) : nat_scope. *)
(* Notation  "2624" := (S 1) : nat_scope. *)
(* Notation  "2625" := (S 1) : nat_scope. *)
(* Notation  "2639" := (S 1) : nat_scope. *)
(* Notation  "2640" := (S 1) : nat_scope. *)
(* Notation  "2649" := (S 1) : nat_scope. *)
(* Notation  "2653" := (S 1) : nat_scope. *)
(* Notation  "2658" := (S 1) : nat_scope. *)
(* Notation  "2659" := (S 1) : nat_scope. *)
(* Notation  "2660" := (S 1) : nat_scope. *)
(* Notation  "2661" := (S 1) : nat_scope. *)
(* Notation  "2675" := (S 1) : nat_scope. *)
(* Notation  "2676" := (S 1) : nat_scope. *)
(* Notation  "2685" := (S 1) : nat_scope. *)
(* Notation  "2689" := (S 1) : nat_scope. *)
(* Notation  "2694" := (S 1) : nat_scope. *)
(* Notation  "2695" := (S 1) : nat_scope. *)
(* Notation  "2696" := (S 1) : nat_scope. *)
(* Notation  "2698" := (S 1) : nat_scope. *)
(* Notation  "2712" := (S 1) : nat_scope. *)
(* Notation  "2713" := (S 1) : nat_scope. *)
(* Notation  "2722" := (S 1) : nat_scope. *)
(* Notation  "2726" := (S 1) : nat_scope. *)
(* Notation  "2731" := (S 1) : nat_scope. *)
(* Notation  "2732" := (S 1) : nat_scope. *)
(* Notation  "2733" := (S 1) : nat_scope. *)
(* Notation  "2735" := (S 1) : nat_scope. *)
(* Notation  "2749" := (S 1) : nat_scope. *)
(* Notation  "2750" := (S 1) : nat_scope. *)
(* Notation  "2759" := (S 1) : nat_scope. *)
(* Notation  "2763" := (S 1) : nat_scope. *)
(* Notation  "2768" := (S 1) : nat_scope. *)
(* Notation  "2769" := (S 1) : nat_scope. *)
(* Notation  "2770" := (S 1) : nat_scope. *)
(* Notation  "2772" := (S 1) : nat_scope. *)
(* Notation  "2786" := (S 1) : nat_scope. *)
(* Notation  "2787" := (S 1) : nat_scope. *)
(* Notation  "2796" := (S 1) : nat_scope. *)
(* Notation  "28" := (S 1) : nat_scope. *)
(* Notation  "2800" := (S 1) : nat_scope. *)
(* Notation  "2805" := (S 1) : nat_scope. *)
(* Notation  "2806" := (S 1) : nat_scope. *)
(* Notation  "2807" := (S 1) : nat_scope. *)
(* Notation  "2809" := (S 1) : nat_scope. *)
(* Notation  "2823" := (S 1) : nat_scope. *)
(* Notation  "2824" := (S 1) : nat_scope. *)
(* Notation  "2833" := (S 1) : nat_scope. *)
(* Notation  "2837" := (S 1) : nat_scope. *)
(* Notation  "2842" := (S 1) : nat_scope. *)
(* Notation  "2843" := (S 1) : nat_scope. *)
(* Notation  "2844" := (S 1) : nat_scope. *)
(* Notation  "2846" := (S 1) : nat_scope. *)
(* Notation  "2860" := (S 1) : nat_scope. *)
(* Notation  "2861" := (S 1) : nat_scope. *)
(* Notation  "2870" := (S 1) : nat_scope. *)
(* Notation  "2874" := (S 1) : nat_scope. *)
(* Notation  "2879" := (S 1) : nat_scope. *)
(* Notation  "2880" := (S 1) : nat_scope. *)
(* Notation  "2881" := (S 1) : nat_scope. *)
(* Notation  "2883" := (S 1) : nat_scope. *)
(* Notation  "2897" := (S 1) : nat_scope. *)
(* Notation  "2898" := (S 1) : nat_scope. *)
(* Notation  "29" := (S 1) : nat_scope. *)
(* Notation  "2907" := (S 1) : nat_scope. *)
(* Notation  "2911" := (S 1) : nat_scope. *)
(* Notation  "2916" := (S 1) : nat_scope. *)
(* Notation  "2917" := (S 1) : nat_scope. *)
(* Notation  "2918" := (S 1) : nat_scope. *)
(* Notation  "2920" := (S 1) : nat_scope. *)
(* Notation  "2934" := (S 1) : nat_scope. *)
(* Notation  "2935" := (S 1) : nat_scope. *)
(* Notation  "2944" := (S 1) : nat_scope. *)
(* Notation  "2948" := (S 1) : nat_scope. *)
(* Notation  "2953" := (S 1) : nat_scope. *)
(* Notation  "2954" := (S 1) : nat_scope. *)
(* Notation  "2955" := (S 1) : nat_scope. *)
(* Notation  "2957" := (S 1) : nat_scope. *)
(* Notation  "2971" := (S 1) : nat_scope. *)
(* Notation  "2972" := (S 1) : nat_scope. *)
(* Notation  "2981" := (S 1) : nat_scope. *)
(* Notation  "2985" := (S 1) : nat_scope. *)
(* Notation  "2990" := (S 1) : nat_scope. *)
(* Notation  "2991" := (S 1) : nat_scope. *)
(* Notation  "2992" := (S 1) : nat_scope. *)
(* Notation  "2994" := (S 1) : nat_scope. *)
(* Notation  "3" := (S 1) : nat_scope. *)
(* Notation  "3008" := (S 1) : nat_scope. *)
(* Notation  "3009" := (S 1) : nat_scope. *)
(* Notation  "3018" := (S 1) : nat_scope. *)
(* Notation  "3022" := (S 1) : nat_scope. *)
(* Notation  "3027" := (S 1) : nat_scope. *)
(* Notation  "3028" := (S 1) : nat_scope. *)
(* Notation  "3029" := (S 1) : nat_scope. *)
(* Notation  "3031" := (S 1) : nat_scope. *)
(* Notation  "3045" := (S 1) : nat_scope. *)
(* Notation  "3046" := (S 1) : nat_scope. *)
(* Notation  "3055" := (S 1) : nat_scope. *)
(* Notation  "3059" := (S 1) : nat_scope. *)
(* Notation  "3064" := (S 1) : nat_scope. *)
(* Notation  "3065" := (S 1) : nat_scope. *)
(* Notation  "3066" := (S 1) : nat_scope. *)
(* Notation  "3068" := (S 1) : nat_scope. *)
(* Notation  "3082" := (S 1) : nat_scope. *)
(* Notation  "3083" := (S 1) : nat_scope. *)
(* Notation  "3092" := (S 1) : nat_scope. *)
(* Notation  "3096" := (S 1) : nat_scope. *)
(* Notation  "3101" := (S 1) : nat_scope. *)
(* Notation  "3102" := (S 1) : nat_scope. *)
(* Notation  "3103" := (S 1) : nat_scope. *)
(* Notation  "3105" := (S 1) : nat_scope. *)
(* Notation  "3119" := (S 1) : nat_scope. *)
(* Notation  "3120" := (S 1) : nat_scope. *)
(* Notation  "3129" := (S 1) : nat_scope. *)
(* Notation  "3133" := (S 1) : nat_scope. *)
(* Notation  "3138" := (S 1) : nat_scope. *)
(* Notation  "3139" := (S 1) : nat_scope. *)
(* Notation  "3140" := (S 1) : nat_scope. *)
(* Notation  "3142" := (S 1) : nat_scope. *)
(* Notation  "3156" := (S 1) : nat_scope. *)
(* Notation  "3157" := (S 1) : nat_scope. *)
(* Notation  "3166" := (S 1) : nat_scope. *)
(* Notation  "3170" := (S 1) : nat_scope. *)
(* Notation  "3175" := (S 1) : nat_scope. *)
(* Notation  "3176" := (S 1) : nat_scope. *)
(* Notation  "3177" := (S 1) : nat_scope. *)
(* Notation  "3179" := (S 1) : nat_scope. *)
(* Notation  "3193" := (S 1) : nat_scope. *)
(* Notation  "3194" := (S 1) : nat_scope. *)
(* Notation  "3203" := (S 1) : nat_scope. *)
(* Notation  "3208" := (S 1) : nat_scope. *)
(* Notation  "3213" := (S 1) : nat_scope. *)
(* Notation  "3215" := (S 1) : nat_scope. *)
(* Notation  "3218" := (S 1) : nat_scope. *)
(* Notation  "3220" := (S 1) : nat_scope. *)
(* Notation  "3234" := (S 1) : nat_scope. *)
(* Notation  "3235" := (S 1) : nat_scope. *)
(* Notation  "3244" := (S 1) : nat_scope. *)
(* Notation  "3250" := (S 1) : nat_scope. *)
(* Notation  "3255" := (S 1) : nat_scope. *)
(* Notation  "3257" := (S 1) : nat_scope. *)
(* Notation  "3260" := (S 1) : nat_scope. *)
(* Notation  "3263" := (S 1) : nat_scope. *)
(* Notation  "3277" := (S 1) : nat_scope. *)
(* Notation  "33" := (S 1) : nat_scope. *)
(* Notation  "3302" := (S 1) : nat_scope. *)
(* Notation  "3312" := (S 1) : nat_scope. *)
(* Notation  "3317" := (S 1) : nat_scope. *)
(* Notation  "3319" := (S 1) : nat_scope. *)
(* Notation  "3320" := (S 1) : nat_scope. *)
(* Notation  "3321" := (S 1) : nat_scope. *)
(* Notation  "3323" := (S 1) : nat_scope. *)
(* Notation  "3326" := (S 1) : nat_scope. *)
(* Notation  "3327" := (S 1) : nat_scope. *)
(* Notation  "3328" := (S 1) : nat_scope. *)
(* Notation  "3329" := (S 1) : nat_scope. *)
(* Notation  "3333" := (S 1) : nat_scope. *)
(* Notation  "3334" := (S 1) : nat_scope. *)
(* Notation  "3338" := (S 1) : nat_scope. *)
(* Notation  "3340" := (S 1) : nat_scope. *)
(* Notation  "3344" := (S 1) : nat_scope. *)
(* Notation  "3354" := (S 1) : nat_scope. *)
(* Notation  "3357" := (S 1) : nat_scope. *)
(* Notation  "3362" := (S 1) : nat_scope. *)
(* Notation  "3363" := (S 1) : nat_scope. *)
(* Notation  "3364" := (S 1) : nat_scope. *)
(* Notation  "3365" := (S 1) : nat_scope. *)
(* Notation  "3366" := (S 1) : nat_scope. *)
(* Notation  "3367" := (S 1) : nat_scope. *)
(* Notation  "3368" := (S 1) : nat_scope. *)
(* Notation  "3370" := (S 1) : nat_scope. *)
(* Notation  "3376" := (S 1) : nat_scope. *)
(* Notation  "3378" := (S 1) : nat_scope. *)
(* Notation  "3391" := (S 1) : nat_scope. *)
(* Notation  "34" := (S 1) : nat_scope. *)
(* Notation  "3401" := (S 1) : nat_scope. *)
(* Notation  "3410" := (S 1) : nat_scope. *)
(* Notation  "3411" := (S 1) : nat_scope. *)
(* Notation  "3420" := (S 1) : nat_scope. *)
(* Notation  "3427" := (S 1) : nat_scope. *)
(* Notation  "3432" := (S 1) : nat_scope. *)
(* Notation  "3437" := (S 1) : nat_scope. *)
(* Notation  "3438" := (S 1) : nat_scope. *)
(* Notation  "3439" := (S 1) : nat_scope. *)
(* Notation  "3440" := (S 1) : nat_scope. *)
(* Notation  "3441" := (S 1) : nat_scope. *)
(* Notation  "3456" := (S 1) : nat_scope. *)
(* Notation  "3457" := (S 1) : nat_scope. *)
(* Notation  "3466" := (S 1) : nat_scope. *)
(* Notation  "3472" := (S 1) : nat_scope. *)
(* Notation  "3476" := (S 1) : nat_scope. *)
(* Notation  "3486" := (S 1) : nat_scope. *)
(* Notation  "3488" := (S 1) : nat_scope. *)
(* Notation  "35" := (S 1) : nat_scope. *)
(* Notation  "37" := (S 1) : nat_scope. *)
(* Notation  "4" := (S 1) : nat_scope. *)
(* Notation  "41" := (S 1) : nat_scope. *)
Definition  a0 := 1%nat : Preamble.nat.
Definition  a00 := 1%nat : Preamble.nat.
Definition  a000 := 1%nat : Preamble.nat.
Definition  a1 := 1%nat : Preamble.nat.
Definition  a10 := 1%nat : Preamble.nat.
Definition  a100 := 1%nat : Preamble.nat.
Definition  a1000 := 1%nat : Preamble.nat.
Definition  a1002 := 1%nat : Preamble.nat.
Definition  a1003 := 1%nat : Preamble.nat.
Definition  a101 := 1%nat : Preamble.nat.
Definition  a1013 := 1%nat : Preamble.nat.
Definition  a1016 := 1%nat : Preamble.nat.
Definition  a1025 := 1%nat : Preamble.nat.
Definition  a1026 := 1%nat : Preamble.nat.
Definition  a103 := 1%nat : Preamble.nat.
Definition  a1036 := 1%nat : Preamble.nat.
Definition  a1039 := 1%nat : Preamble.nat.
Definition  a104 := 1%nat : Preamble.nat.
Definition  a1048 := 1%nat : Preamble.nat.
Definition  a105 := 1%nat : Preamble.nat.
Definition  a1050 := 1%nat : Preamble.nat.
Definition  a1059 := 1%nat : Preamble.nat.
Definition  a106 := 1%nat : Preamble.nat.
Definition  a1062 := 1%nat : Preamble.nat.
Definition  a1066 := 1%nat : Preamble.nat.
Definition  a1069 := 1%nat : Preamble.nat.
Definition  a107 := 1%nat : Preamble.nat.
Definition  a1070 := 1%nat : Preamble.nat.
Definition  a108 := 1%nat : Preamble.nat.
Definition  a11 := 1%nat : Preamble.nat.
Definition  a110 := 1%nat : Preamble.nat.
Definition  a111 := 1%nat : Preamble.nat.
Definition  a112 := 1%nat : Preamble.nat.
Definition  a1127 := 1%nat : Preamble.nat.
Definition  a113 := 1%nat : Preamble.nat.
Definition  a1136 := 1%nat : Preamble.nat.
Definition  a1139 := 1%nat : Preamble.nat.
Definition  a114 := 1%nat : Preamble.nat.
Definition  a1143 := 1%nat : Preamble.nat.
Definition  a1146 := 1%nat : Preamble.nat.
Definition  a1147 := 1%nat : Preamble.nat.
Definition  a115 := 1%nat : Preamble.nat.
Definition  a116 := 1%nat : Preamble.nat.
Definition  a117 := 1%nat : Preamble.nat.
Definition  a118 := 1%nat : Preamble.nat.
Definition  a119 := 1%nat : Preamble.nat.
Definition  a12 := 1%nat : Preamble.nat.
Definition  a120 := 1%nat : Preamble.nat.
Definition  a1205 := 1%nat : Preamble.nat.
Definition  a121 := 1%nat : Preamble.nat.
Definition  a1214 := 1%nat : Preamble.nat.
Definition  a122 := 1%nat : Preamble.nat.
Definition  a1223 := 1%nat : Preamble.nat.
Definition  a1228 := 1%nat : Preamble.nat.
Definition  a123 := 1%nat : Preamble.nat.
Definition  a1234 := 1%nat : Preamble.nat.
Definition  a1235 := 1%nat : Preamble.nat.
Definition  a1236 := 1%nat : Preamble.nat.
Definition  a1237 := 1%nat : Preamble.nat.
Definition  a1238 := 1%nat : Preamble.nat.
Definition  a124 := 1%nat : Preamble.nat.
Definition  a1240 := 1%nat : Preamble.nat.
Definition  a125 := 1%nat : Preamble.nat.
Definition  a126 := 1%nat : Preamble.nat.
Definition  a127 := 1%nat : Preamble.nat.
Definition  a128 := 1%nat : Preamble.nat.
Definition  a129 := 1%nat : Preamble.nat.
Definition  a13 := 1%nat : Preamble.nat.
Definition  a130 := 1%nat : Preamble.nat.
Definition  a131 := 1%nat : Preamble.nat.
Definition  a132 := 1%nat : Preamble.nat.
Definition  a133 := 1%nat : Preamble.nat.
Definition  a134 := 1%nat : Preamble.nat.
Definition  a135 := 1%nat : Preamble.nat.
Definition  a136 := 1%nat : Preamble.nat.
Definition  a1382 := 1%nat : Preamble.nat.
Definition  a1392 := 1%nat : Preamble.nat.
Definition  a1395 := 1%nat : Preamble.nat.
Definition  a1398 := 1%nat : Preamble.nat.
Definition  a14 := 1%nat : Preamble.nat.
Definition  a140 := 1%nat : Preamble.nat.
Definition  a1400 := 1%nat : Preamble.nat.
Definition  a1404 := 1%nat : Preamble.nat.
Definition  a1408 := 1%nat : Preamble.nat.
Definition  a1409 := 1%nat : Preamble.nat.
Definition  a141 := 1%nat : Preamble.nat.
Definition  a1412 := 1%nat : Preamble.nat.
Definition  a1415 := 1%nat : Preamble.nat.
Definition  a1416 := 1%nat : Preamble.nat.
Definition  a142 := 1%nat : Preamble.nat.
Definition  a1420 := 1%nat : Preamble.nat.
Definition  a1421 := 1%nat : Preamble.nat.
Definition  a1424 := 1%nat : Preamble.nat.
Definition  a1427 := 1%nat : Preamble.nat.
Definition  a143 := 1%nat : Preamble.nat.
Definition  a1431 := 1%nat : Preamble.nat.
Definition  a1434 := 1%nat : Preamble.nat.
Definition  a1435 := 1%nat : Preamble.nat.
Definition  a1437 := 1%nat : Preamble.nat.
Definition  a144 := 1%nat : Preamble.nat.
Definition  a1448 := 1%nat : Preamble.nat.
Definition  a1452 := 1%nat : Preamble.nat.
Definition  a1456 := 1%nat : Preamble.nat.
Definition  a1457 := 1%nat : Preamble.nat.
Definition  a1458 := 1%nat : Preamble.nat.
Definition  a1460 := 1%nat : Preamble.nat.
Definition  a1484 := 1%nat : Preamble.nat.
Definition  a1485 := 1%nat : Preamble.nat.
Definition  a15 := 1%nat : Preamble.nat.
Definition  a1518 := 1%nat : Preamble.nat.
Definition  a1519 := 1%nat : Preamble.nat.
Definition  a1545 := 1%nat : Preamble.nat.
Definition  a1548 := 1%nat : Preamble.nat.
Definition  a1549 := 1%nat : Preamble.nat.
Definition  a1550 := 1%nat : Preamble.nat.
Definition  a1560 := 1%nat : Preamble.nat.
Definition  a1561 := 1%nat : Preamble.nat.
Definition  a1562 := 1%nat : Preamble.nat.
Definition  a1567 := 1%nat : Preamble.nat.
Definition  a1568 := 1%nat : Preamble.nat.
Definition  a1569 := 1%nat : Preamble.nat.
Definition  a1590 := 1%nat : Preamble.nat.
Definition  a1592 := 1%nat : Preamble.nat.
Definition  a16 := 1%nat : Preamble.nat.
Definition  a1601 := 1%nat : Preamble.nat.
Definition  a1604 := 1%nat : Preamble.nat.
Definition  a1605 := 1%nat : Preamble.nat.
Definition  a1606 := 1%nat : Preamble.nat.
Definition  a1607 := 1%nat : Preamble.nat.
Definition  a1608 := 1%nat : Preamble.nat.
Definition  a1612 := 1%nat : Preamble.nat.
Definition  a1614 := 1%nat : Preamble.nat.
Definition  a1620 := 1%nat : Preamble.nat.
Definition  a1621 := 1%nat : Preamble.nat.
Definition  a1627 := 1%nat : Preamble.nat.
Definition  a1631 := 1%nat : Preamble.nat.
Definition  a1632 := 1%nat : Preamble.nat.
Definition  a1636 := 1%nat : Preamble.nat.
Definition  a1637 := 1%nat : Preamble.nat.
Definition  a1638 := 1%nat : Preamble.nat.
Definition  a1642 := 1%nat : Preamble.nat.
Definition  a1643 := 1%nat : Preamble.nat.
Definition  a1644 := 1%nat : Preamble.nat.
Definition  a1645 := 1%nat : Preamble.nat.
Definition  a1649 := 1%nat : Preamble.nat.
Definition  a1650 := 1%nat : Preamble.nat.
Definition  a1652 := 1%nat : Preamble.nat.
Definition  a1653 := 1%nat : Preamble.nat.
Definition  a1656 := 1%nat : Preamble.nat.
Definition  a1657 := 1%nat : Preamble.nat.
Definition  a1658 := 1%nat : Preamble.nat.
Definition  a1659 := 1%nat : Preamble.nat.
Definition  a1664 := 1%nat : Preamble.nat.
Definition  a1665 := 1%nat : Preamble.nat.
Definition  a1671 := 1%nat : Preamble.nat.
Definition  a1678 := 1%nat : Preamble.nat.
Definition  a1683 := 1%nat : Preamble.nat.
Definition  a1686 := 1%nat : Preamble.nat.
Definition  a1687 := 1%nat : Preamble.nat.
Definition  a1688 := 1%nat : Preamble.nat.
Definition  a1689 := 1%nat : Preamble.nat.
Definition  a1690 := 1%nat : Preamble.nat.
Definition  a17 := 1%nat : Preamble.nat.
Definition  a1704 := 1%nat : Preamble.nat.
Definition  a1706 := 1%nat : Preamble.nat.
Definition  a1715 := 1%nat : Preamble.nat.
Definition  a1718 := 1%nat : Preamble.nat.
Definition  a1719 := 1%nat : Preamble.nat.
Definition  a1720 := 1%nat : Preamble.nat.
Definition  a1721 := 1%nat : Preamble.nat.
Definition  a1722 := 1%nat : Preamble.nat.
Definition  a1726 := 1%nat : Preamble.nat.
Definition  a1728 := 1%nat : Preamble.nat.
Definition  a1734 := 1%nat : Preamble.nat.
Definition  a1735 := 1%nat : Preamble.nat.
Definition  a1737 := 1%nat : Preamble.nat.
Definition  a1738 := 1%nat : Preamble.nat.
Definition  a1744 := 1%nat : Preamble.nat.
Definition  a1748 := 1%nat : Preamble.nat.
Definition  a1749 := 1%nat : Preamble.nat.
Definition  a1750 := 1%nat : Preamble.nat.
Definition  a1751 := 1%nat : Preamble.nat.
Definition  a1753 := 1%nat : Preamble.nat.
Definition  a1754 := 1%nat : Preamble.nat.
Definition  a1755 := 1%nat : Preamble.nat.
Definition  a1756 := 1%nat : Preamble.nat.
Definition  a1760 := 1%nat : Preamble.nat.
Definition  a1761 := 1%nat : Preamble.nat.
Definition  a1764 := 1%nat : Preamble.nat.
Definition  a1765 := 1%nat : Preamble.nat.
Definition  a1766 := 1%nat : Preamble.nat.
Definition  a1770 := 1%nat : Preamble.nat.
Definition  a1771 := 1%nat : Preamble.nat.
Definition  a1773 := 1%nat : Preamble.nat.
Definition  a1774 := 1%nat : Preamble.nat.
Definition  a1778 := 1%nat : Preamble.nat.
Definition  a1779 := 1%nat : Preamble.nat.
Definition  a178 := 1%nat : Preamble.nat.
Definition  a1780 := 1%nat : Preamble.nat.
Definition  a1785 := 1%nat : Preamble.nat.
Definition  a1786 := 1%nat : Preamble.nat.
Definition  a179 := 1%nat : Preamble.nat.
Definition  a1792 := 1%nat : Preamble.nat.
Definition  a1799 := 1%nat : Preamble.nat.
Definition  a18 := 1%nat : Preamble.nat.
Definition  a1804 := 1%nat : Preamble.nat.
Definition  a1807 := 1%nat : Preamble.nat.
Definition  a1808 := 1%nat : Preamble.nat.
Definition  a1809 := 1%nat : Preamble.nat.
Definition  a181 := 1%nat : Preamble.nat.
Definition  a1810 := 1%nat : Preamble.nat.
Definition  a1811 := 1%nat : Preamble.nat.
Definition  a1825 := 1%nat : Preamble.nat.
Definition  a183 := 1%nat : Preamble.nat.
Definition  a184 := 1%nat : Preamble.nat.
Definition  a185 := 1%nat : Preamble.nat.
Definition  a187 := 1%nat : Preamble.nat.
Definition  a188 := 1%nat : Preamble.nat.
Definition  a1882 := 1%nat : Preamble.nat.
Definition  a1893 := 1%nat : Preamble.nat.
Definition  a1896 := 1%nat : Preamble.nat.
Definition  a1899 := 1%nat : Preamble.nat.
Definition  a19 := 1%nat : Preamble.nat.
Definition  a1902 := 1%nat : Preamble.nat.
Definition  a1906 := 1%nat : Preamble.nat.
Definition  a1909 := 1%nat : Preamble.nat.
Definition  a1913 := 1%nat : Preamble.nat.
Definition  a1916 := 1%nat : Preamble.nat.
Definition  a1917 := 1%nat : Preamble.nat.
Definition  a1918 := 1%nat : Preamble.nat.
Definition  a1924 := 1%nat : Preamble.nat.
Definition  a1925 := 1%nat : Preamble.nat.
Definition  a1927 := 1%nat : Preamble.nat.
Definition  a1934 := 1%nat : Preamble.nat.
Definition  a1935 := 1%nat : Preamble.nat.
Definition  a1936 := 1%nat : Preamble.nat.
Definition  a1937 := 1%nat : Preamble.nat.
Definition  a1938 := 1%nat : Preamble.nat.
Definition  a1939 := 1%nat : Preamble.nat.
Definition  a1941 := 1%nat : Preamble.nat.
Definition  a1951 := 1%nat : Preamble.nat.
Definition  a1952 := 1%nat : Preamble.nat.
Definition  a1956 := 1%nat : Preamble.nat.
Definition  a1958 := 1%nat : Preamble.nat.
Definition  a1959 := 1%nat : Preamble.nat.
Definition  a1960 := 1%nat : Preamble.nat.
Definition  a1962 := 1%nat : Preamble.nat.
Definition  a1963 := 1%nat : Preamble.nat.
Definition  a1964 := 1%nat : Preamble.nat.
Definition  a1965 := 1%nat : Preamble.nat.
Definition  a1967 := 1%nat : Preamble.nat.
Definition  a1968 := 1%nat : Preamble.nat.
Definition  a1969 := 1%nat : Preamble.nat.
Definition  a1975 := 1%nat : Preamble.nat.
Definition  a1976 := 1%nat : Preamble.nat.
Definition  a1977 := 1%nat : Preamble.nat.
Definition  a1978 := 1%nat : Preamble.nat.
Definition  a1980 := 1%nat : Preamble.nat.
Definition  a1981 := 1%nat : Preamble.nat.
Definition  a1982 := 1%nat : Preamble.nat.
Definition  a1989 := 1%nat : Preamble.nat.
Definition  a1991 := 1%nat : Preamble.nat.
Definition  a1994 := 1%nat : Preamble.nat.
Definition  a1995 := 1%nat : Preamble.nat.
Definition  a1996 := 1%nat : Preamble.nat.
Definition  a1997 := 1%nat : Preamble.nat.
Definition  a1998 := 1%nat : Preamble.nat.
Definition  a2 := 1%nat : Preamble.nat.
Definition  a20 := 1%nat : Preamble.nat.
Definition  a200 := 1%nat : Preamble.nat.
Definition  a2006 := 1%nat : Preamble.nat.
Definition  a2008 := 1%nat : Preamble.nat.
Definition  a2017 := 1%nat : Preamble.nat.
Definition  a2024 := 1%nat : Preamble.nat.
Definition  a2029 := 1%nat : Preamble.nat.
Definition  a2032 := 1%nat : Preamble.nat.
Definition  a2033 := 1%nat : Preamble.nat.
Definition  a2034 := 1%nat : Preamble.nat.
Definition  a2035 := 1%nat : Preamble.nat.
Definition  a2036 := 1%nat : Preamble.nat.
Definition  a2050 := 1%nat : Preamble.nat.
Definition  a2052 := 1%nat : Preamble.nat.
Definition  a2061 := 1%nat : Preamble.nat.
Definition  a2064 := 1%nat : Preamble.nat.
Definition  a2065 := 1%nat : Preamble.nat.
Definition  a2066 := 1%nat : Preamble.nat.
Definition  a2067 := 1%nat : Preamble.nat.
Definition  a2068 := 1%nat : Preamble.nat.
Definition  a2072 := 1%nat : Preamble.nat.
Definition  a2074 := 1%nat : Preamble.nat.
Definition  a2080 := 1%nat : Preamble.nat.
Definition  a2081 := 1%nat : Preamble.nat.
Definition  a2083 := 1%nat : Preamble.nat.
Definition  a2084 := 1%nat : Preamble.nat.
Definition  a2090 := 1%nat : Preamble.nat.
Definition  a2096 := 1%nat : Preamble.nat.
Definition  a2097 := 1%nat : Preamble.nat.
Definition  a2099 := 1%nat : Preamble.nat.
Definition  a21 := 1%nat : Preamble.nat.
Definition  a2100 := 1%nat : Preamble.nat.
Definition  a2104 := 1%nat : Preamble.nat.
Definition  a2105 := 1%nat : Preamble.nat.
Definition  a2106 := 1%nat : Preamble.nat.
Definition  a2112 := 1%nat : Preamble.nat.
Definition  a2113 := 1%nat : Preamble.nat.
Definition  a2114 := 1%nat : Preamble.nat.
Definition  a2116 := 1%nat : Preamble.nat.
Definition  a2118 := 1%nat : Preamble.nat.
Definition  a2119 := 1%nat : Preamble.nat.
Definition  a2123 := 1%nat : Preamble.nat.
Definition  a2124 := 1%nat : Preamble.nat.
Definition  a2125 := 1%nat : Preamble.nat.
Definition  a2131 := 1%nat : Preamble.nat.
Definition  a2132 := 1%nat : Preamble.nat.
Definition  a2133 := 1%nat : Preamble.nat.
Definition  a2135 := 1%nat : Preamble.nat.
Definition  a2137 := 1%nat : Preamble.nat.
Definition  a2138 := 1%nat : Preamble.nat.
Definition  a2139 := 1%nat : Preamble.nat.
Definition  a2141 := 1%nat : Preamble.nat.
Definition  a2145 := 1%nat : Preamble.nat.
Definition  a2146 := 1%nat : Preamble.nat.
Definition  a2148 := 1%nat : Preamble.nat.
Definition  a2151 := 1%nat : Preamble.nat.
Definition  a2152 := 1%nat : Preamble.nat.
Definition  a2154 := 1%nat : Preamble.nat.
Definition  a2155 := 1%nat : Preamble.nat.
Definition  a2157 := 1%nat : Preamble.nat.
Definition  a2158 := 1%nat : Preamble.nat.
Definition  a2159 := 1%nat : Preamble.nat.
Definition  a2164 := 1%nat : Preamble.nat.
Definition  a2165 := 1%nat : Preamble.nat.
Definition  a2167 := 1%nat : Preamble.nat.
Definition  a2176 := 1%nat : Preamble.nat.
Definition  a2179 := 1%nat : Preamble.nat.
Definition  a2180 := 1%nat : Preamble.nat.
Definition  a2181 := 1%nat : Preamble.nat.
Definition  a2182 := 1%nat : Preamble.nat.
Definition  a2183 := 1%nat : Preamble.nat.
Definition  a2187 := 1%nat : Preamble.nat.
Definition  a2189 := 1%nat : Preamble.nat.
Definition  a2195 := 1%nat : Preamble.nat.
Definition  a2196 := 1%nat : Preamble.nat.
Definition  a2198 := 1%nat : Preamble.nat.
Definition  a2199 := 1%nat : Preamble.nat.
Definition  a22 := 1%nat : Preamble.nat.
Definition  a2205 := 1%nat : Preamble.nat.
Definition  a2211 := 1%nat : Preamble.nat.
Definition  a2212 := 1%nat : Preamble.nat.
Definition  a2214 := 1%nat : Preamble.nat.
Definition  a2215 := 1%nat : Preamble.nat.
Definition  a2219 := 1%nat : Preamble.nat.
Definition  a2220 := 1%nat : Preamble.nat.
Definition  a2221 := 1%nat : Preamble.nat.
Definition  a2227 := 1%nat : Preamble.nat.
Definition  a2228 := 1%nat : Preamble.nat.
Definition  a2229 := 1%nat : Preamble.nat.
Definition  a2231 := 1%nat : Preamble.nat.
Definition  a2233 := 1%nat : Preamble.nat.
Definition  a2234 := 1%nat : Preamble.nat.
Definition  a2238 := 1%nat : Preamble.nat.
Definition  a2239 := 1%nat : Preamble.nat.
Definition  a2240 := 1%nat : Preamble.nat.
Definition  a2246 := 1%nat : Preamble.nat.
Definition  a2247 := 1%nat : Preamble.nat.
Definition  a2248 := 1%nat : Preamble.nat.
Definition  a2250 := 1%nat : Preamble.nat.
Definition  a2252 := 1%nat : Preamble.nat.
Definition  a2253 := 1%nat : Preamble.nat.
Definition  a2254 := 1%nat : Preamble.nat.
Definition  a2256 := 1%nat : Preamble.nat.
Definition  a2260 := 1%nat : Preamble.nat.
Definition  a2261 := 1%nat : Preamble.nat.
Definition  a2263 := 1%nat : Preamble.nat.
Definition  a2266 := 1%nat : Preamble.nat.
Definition  a2267 := 1%nat : Preamble.nat.
Definition  a2269 := 1%nat : Preamble.nat.
Definition  a2270 := 1%nat : Preamble.nat.
Definition  a2272 := 1%nat : Preamble.nat.
Definition  a2273 := 1%nat : Preamble.nat.
Definition  a2274 := 1%nat : Preamble.nat.
Definition  a2279 := 1%nat : Preamble.nat.
Definition  a2280 := 1%nat : Preamble.nat.
Definition  a2282 := 1%nat : Preamble.nat.
Definition  a2292 := 1%nat : Preamble.nat.
Definition  a2295 := 1%nat : Preamble.nat.
Definition  a23 := 1%nat : Preamble.nat.
Definition  a2300 := 1%nat : Preamble.nat.
Definition  a2301 := 1%nat : Preamble.nat.
Definition  a2315 := 1%nat : Preamble.nat.
Definition  a2316 := 1%nat : Preamble.nat.
Definition  a2326 := 1%nat : Preamble.nat.
Definition  a2329 := 1%nat : Preamble.nat.
Definition  a2334 := 1%nat : Preamble.nat.
Definition  a2335 := 1%nat : Preamble.nat.
Definition  a2336 := 1%nat : Preamble.nat.
Definition  a2337 := 1%nat : Preamble.nat.
Definition  a2351 := 1%nat : Preamble.nat.
Definition  a2352 := 1%nat : Preamble.nat.
Definition  a2362 := 1%nat : Preamble.nat.
Definition  a2365 := 1%nat : Preamble.nat.
Definition  a2370 := 1%nat : Preamble.nat.
Definition  a2371 := 1%nat : Preamble.nat.
Definition  a2372 := 1%nat : Preamble.nat.
Definition  a2373 := 1%nat : Preamble.nat.
Definition  a2387 := 1%nat : Preamble.nat.
Definition  a2388 := 1%nat : Preamble.nat.
Definition  a2398 := 1%nat : Preamble.nat.
Definition  a24 := 1%nat : Preamble.nat.
Definition  a2401 := 1%nat : Preamble.nat.
Definition  a2406 := 1%nat : Preamble.nat.
Definition  a2407 := 1%nat : Preamble.nat.
Definition  a2408 := 1%nat : Preamble.nat.
Definition  a2409 := 1%nat : Preamble.nat.
Definition  a2423 := 1%nat : Preamble.nat.
Definition  a2424 := 1%nat : Preamble.nat.
Definition  a2434 := 1%nat : Preamble.nat.
Definition  a2437 := 1%nat : Preamble.nat.
Definition  a2442 := 1%nat : Preamble.nat.
Definition  a2443 := 1%nat : Preamble.nat.
Definition  a2444 := 1%nat : Preamble.nat.
Definition  a2445 := 1%nat : Preamble.nat.
Definition  a2459 := 1%nat : Preamble.nat.
Definition  a2460 := 1%nat : Preamble.nat.
Definition  a2470 := 1%nat : Preamble.nat.
Definition  a2473 := 1%nat : Preamble.nat.
Definition  a2478 := 1%nat : Preamble.nat.
Definition  a2479 := 1%nat : Preamble.nat.
Definition  a2480 := 1%nat : Preamble.nat.
Definition  a2481 := 1%nat : Preamble.nat.
Definition  a2495 := 1%nat : Preamble.nat.
Definition  a2496 := 1%nat : Preamble.nat.
Definition  a2506 := 1%nat : Preamble.nat.
Definition  a2509 := 1%nat : Preamble.nat.
Definition  a2514 := 1%nat : Preamble.nat.
Definition  a2515 := 1%nat : Preamble.nat.
Definition  a2516 := 1%nat : Preamble.nat.
Definition  a2517 := 1%nat : Preamble.nat.
Definition  a2531 := 1%nat : Preamble.nat.
Definition  a2532 := 1%nat : Preamble.nat.
Definition  a2542 := 1%nat : Preamble.nat.
Definition  a2545 := 1%nat : Preamble.nat.
Definition  a2550 := 1%nat : Preamble.nat.
Definition  a2551 := 1%nat : Preamble.nat.
Definition  a2552 := 1%nat : Preamble.nat.
Definition  a2553 := 1%nat : Preamble.nat.
Definition  a2567 := 1%nat : Preamble.nat.
Definition  a2568 := 1%nat : Preamble.nat.
Definition  a2578 := 1%nat : Preamble.nat.
Definition  a2581 := 1%nat : Preamble.nat.
Definition  a2586 := 1%nat : Preamble.nat.
Definition  a2587 := 1%nat : Preamble.nat.
Definition  a2588 := 1%nat : Preamble.nat.
Definition  a2589 := 1%nat : Preamble.nat.
Definition  a2603 := 1%nat : Preamble.nat.
Definition  a2604 := 1%nat : Preamble.nat.
Definition  a2614 := 1%nat : Preamble.nat.
Definition  a2617 := 1%nat : Preamble.nat.
Definition  a2622 := 1%nat : Preamble.nat.
Definition  a2623 := 1%nat : Preamble.nat.
Definition  a2624 := 1%nat : Preamble.nat.
Definition  a2625 := 1%nat : Preamble.nat.
Definition  a2639 := 1%nat : Preamble.nat.
Definition  a2640 := 1%nat : Preamble.nat.
Definition  a2649 := 1%nat : Preamble.nat.
Definition  a2653 := 1%nat : Preamble.nat.
Definition  a2658 := 1%nat : Preamble.nat.
Definition  a2659 := 1%nat : Preamble.nat.
Definition  a2660 := 1%nat : Preamble.nat.
Definition  a2661 := 1%nat : Preamble.nat.
Definition  a2675 := 1%nat : Preamble.nat.
Definition  a2676 := 1%nat : Preamble.nat.
Definition  a2685 := 1%nat : Preamble.nat.
Definition  a2689 := 1%nat : Preamble.nat.
Definition  a2694 := 1%nat : Preamble.nat.
Definition  a2695 := 1%nat : Preamble.nat.
Definition  a2696 := 1%nat : Preamble.nat.
Definition  a2698 := 1%nat : Preamble.nat.
Definition  a2712 := 1%nat : Preamble.nat.
Definition  a2713 := 1%nat : Preamble.nat.
Definition  a2722 := 1%nat : Preamble.nat.
Definition  a2726 := 1%nat : Preamble.nat.
Definition  a2731 := 1%nat : Preamble.nat.
Definition  a2732 := 1%nat : Preamble.nat.
Definition  a2733 := 1%nat : Preamble.nat.
Definition  a2735 := 1%nat : Preamble.nat.
Definition  a2749 := 1%nat : Preamble.nat.
Definition  a2750 := 1%nat : Preamble.nat.
Definition  a2759 := 1%nat : Preamble.nat.
Definition  a2763 := 1%nat : Preamble.nat.
Definition  a2768 := 1%nat : Preamble.nat.
Definition  a2769 := 1%nat : Preamble.nat.
Definition  a2770 := 1%nat : Preamble.nat.
Definition  a2772 := 1%nat : Preamble.nat.
Definition  a2786 := 1%nat : Preamble.nat.
Definition  a2787 := 1%nat : Preamble.nat.
Definition  a2796 := 1%nat : Preamble.nat.
Definition  a28 := 1%nat : Preamble.nat.
Definition  a2800 := 1%nat : Preamble.nat.
Definition  a2805 := 1%nat : Preamble.nat.
Definition  a2806 := 1%nat : Preamble.nat.
Definition  a2807 := 1%nat : Preamble.nat.
Definition  a2809 := 1%nat : Preamble.nat.
Definition  a2823 := 1%nat : Preamble.nat.
Definition  a2824 := 1%nat : Preamble.nat.
Definition  a2833 := 1%nat : Preamble.nat.
Definition  a2837 := 1%nat : Preamble.nat.
Definition  a2842 := 1%nat : Preamble.nat.
Definition  a2843 := 1%nat : Preamble.nat.
Definition  a2844 := 1%nat : Preamble.nat.
Definition  a2846 := 1%nat : Preamble.nat.
Definition  a2860 := 1%nat : Preamble.nat.
Definition  a2861 := 1%nat : Preamble.nat.
Definition  a2870 := 1%nat : Preamble.nat.
Definition  a2874 := 1%nat : Preamble.nat.
Definition  a2879 := 1%nat : Preamble.nat.
Definition  a2880 := 1%nat : Preamble.nat.
Definition  a2881 := 1%nat : Preamble.nat.
Definition  a2883 := 1%nat : Preamble.nat.
Definition  a2897 := 1%nat : Preamble.nat.
Definition  a2898 := 1%nat : Preamble.nat.
Definition  a29 := 1%nat : Preamble.nat.
Definition  a2907 := 1%nat : Preamble.nat.
Definition  a2911 := 1%nat : Preamble.nat.
Definition  a2916 := 1%nat : Preamble.nat.
Definition  a2917 := 1%nat : Preamble.nat.
Definition  a2918 := 1%nat : Preamble.nat.
Definition  a2920 := 1%nat : Preamble.nat.
Definition  a2934 := 1%nat : Preamble.nat.
Definition  a2935 := 1%nat : Preamble.nat.
Definition  a2944 := 1%nat : Preamble.nat.
Definition  a2948 := 1%nat : Preamble.nat.
Definition  a2953 := 1%nat : Preamble.nat.
Definition  a2954 := 1%nat : Preamble.nat.
Definition  a2955 := 1%nat : Preamble.nat.
Definition  a2957 := 1%nat : Preamble.nat.
Definition  a2971 := 1%nat : Preamble.nat.
Definition  a2972 := 1%nat : Preamble.nat.
Definition  a2981 := 1%nat : Preamble.nat.
Definition  a2985 := 1%nat : Preamble.nat.
Definition  a2990 := 1%nat : Preamble.nat.
Definition  a2991 := 1%nat : Preamble.nat.
Definition  a2992 := 1%nat : Preamble.nat.
Definition  a2994 := 1%nat : Preamble.nat.
Definition  a3 := 1%nat : Preamble.nat.
Definition  a3008 := 1%nat : Preamble.nat.
Definition  a3009 := 1%nat : Preamble.nat.
Definition  a3018 := 1%nat : Preamble.nat.
Definition  a3022 := 1%nat : Preamble.nat.
Definition  a3027 := 1%nat : Preamble.nat.
Definition  a3028 := 1%nat : Preamble.nat.
Definition  a3029 := 1%nat : Preamble.nat.
Definition  a3031 := 1%nat : Preamble.nat.
Definition  a3045 := 1%nat : Preamble.nat.
Definition  a3046 := 1%nat : Preamble.nat.
Definition  a3055 := 1%nat : Preamble.nat.
Definition  a3059 := 1%nat : Preamble.nat.
Definition  a3064 := 1%nat : Preamble.nat.
Definition  a3065 := 1%nat : Preamble.nat.
Definition  a3066 := 1%nat : Preamble.nat.
Definition  a3068 := 1%nat : Preamble.nat.
Definition  a3082 := 1%nat : Preamble.nat.
Definition  a3083 := 1%nat : Preamble.nat.
Definition  a3092 := 1%nat : Preamble.nat.
Definition  a3096 := 1%nat : Preamble.nat.
Definition  a3101 := 1%nat : Preamble.nat.
Definition  a3102 := 1%nat : Preamble.nat.
Definition  a3103 := 1%nat : Preamble.nat.
Definition  a3105 := 1%nat : Preamble.nat.
Definition  a3119 := 1%nat : Preamble.nat.
Definition  a3120 := 1%nat : Preamble.nat.
Definition  a3129 := 1%nat : Preamble.nat.
Definition  a3133 := 1%nat : Preamble.nat.
Definition  a3138 := 1%nat : Preamble.nat.
Definition  a3139 := 1%nat : Preamble.nat.
Definition  a3140 := 1%nat : Preamble.nat.
Definition  a3142 := 1%nat : Preamble.nat.
Definition  a3156 := 1%nat : Preamble.nat.
Definition  a3157 := 1%nat : Preamble.nat.
Definition  a3166 := 1%nat : Preamble.nat.
Definition  a3170 := 1%nat : Preamble.nat.
Definition  a3175 := 1%nat : Preamble.nat.
Definition  a3176 := 1%nat : Preamble.nat.
Definition  a3177 := 1%nat : Preamble.nat.
Definition  a3179 := 1%nat : Preamble.nat.
Definition  a3193 := 1%nat : Preamble.nat.
Definition  a3194 := 1%nat : Preamble.nat.
Definition  a3203 := 1%nat : Preamble.nat.
Definition  a3208 := 1%nat : Preamble.nat.
Definition  a3213 := 1%nat : Preamble.nat.
Definition  a3215 := 1%nat : Preamble.nat.
Definition  a3218 := 1%nat : Preamble.nat.
Definition  a3220 := 1%nat : Preamble.nat.
Definition  a3234 := 1%nat : Preamble.nat.
Definition  a3235 := 1%nat : Preamble.nat.
Definition  a3244 := 1%nat : Preamble.nat.
Definition  a3250 := 1%nat : Preamble.nat.
Definition  a3255 := 1%nat : Preamble.nat.
Definition  a3257 := 1%nat : Preamble.nat.
Definition  a3260 := 1%nat : Preamble.nat.
Definition  a3263 := 1%nat : Preamble.nat.
Definition  a3277 := 1%nat : Preamble.nat.
Definition  a33 := 1%nat : Preamble.nat.
Definition  a3302 := 1%nat : Preamble.nat.
Definition  a3312 := 1%nat : Preamble.nat.
Definition  a3317 := 1%nat : Preamble.nat.
Definition  a3319 := 1%nat : Preamble.nat.
Definition  a3320 := 1%nat : Preamble.nat.
Definition  a3321 := 1%nat : Preamble.nat.
Definition  a3323 := 1%nat : Preamble.nat.
Definition  a3326 := 1%nat : Preamble.nat.
Definition  a3327 := 1%nat : Preamble.nat.
Definition  a3328 := 1%nat : Preamble.nat.
Definition  a3329 := 1%nat : Preamble.nat.
Definition  a3333 := 1%nat : Preamble.nat.
Definition  a3334 := 1%nat : Preamble.nat.
Definition  a3338 := 1%nat : Preamble.nat.
Definition  a3340 := 1%nat : Preamble.nat.
Definition  a3344 := 1%nat : Preamble.nat.
Definition  a3354 := 1%nat : Preamble.nat.
Definition  a3357 := 1%nat : Preamble.nat.
Definition  a3362 := 1%nat : Preamble.nat.
Definition  a3363 := 1%nat : Preamble.nat.
Definition  a3364 := 1%nat : Preamble.nat.
Definition  a3365 := 1%nat : Preamble.nat.
Definition  a3366 := 1%nat : Preamble.nat.
Definition  a3367 := 1%nat : Preamble.nat.
Definition  a3368 := 1%nat : Preamble.nat.
Definition  a3370 := 1%nat : Preamble.nat.
Definition  a3376 := 1%nat : Preamble.nat.
Definition  a3378 := 1%nat : Preamble.nat.
Definition  a3391 := 1%nat : Preamble.nat.
Definition  a34 := 1%nat : Preamble.nat.
Definition  a3401 := 1%nat : Preamble.nat.
Definition  a3410 := 1%nat : Preamble.nat.
Definition  a3411 := 1%nat : Preamble.nat.
Definition  a3420 := 1%nat : Preamble.nat.
Definition  a3427 := 1%nat : Preamble.nat.
Definition  a3432 := 1%nat : Preamble.nat.
Definition  a3437 := 1%nat : Preamble.nat.
Definition  a3438 := 1%nat : Preamble.nat.
Definition  a3439 := 1%nat : Preamble.nat.
Definition  a3440 := 1%nat : Preamble.nat.
Definition  a3441 := 1%nat : Preamble.nat.
Definition  a3456 := 1%nat : Preamble.nat.
Definition  a3457 := 1%nat : Preamble.nat.
Definition  a3466 := 1%nat : Preamble.nat.
Definition  a3472 := 1%nat : Preamble.nat.
Definition  a3476 := 1%nat : Preamble.nat.
Definition  a3486 := 1%nat : Preamble.nat.
Definition  a3488 := 1%nat : Preamble.nat.
Definition  a35 := 1%nat : Preamble.nat.
Definition  a37 := 1%nat : Preamble.nat.
Definition  a4 := 1%nat : Preamble.nat.
Definition  a41 := 1%nat : Preamble.nat.
Definition  a415 := 1%nat : Preamble.nat.
Definition  a42 := 1%nat : Preamble.nat.
Definition  a43 := 1%nat : Preamble.nat.
Definition  a430 := 1%nat : Preamble.nat.
Definition  a45 := 1%nat : Preamble.nat.
Definition  a454 := 1%nat : Preamble.nat.
Definition  a455 := 1%nat : Preamble.nat.
Definition  a46 := 1%nat : Preamble.nat.
Definition  a47 := 1%nat : Preamble.nat.
Definition  a484 := 1%nat : Preamble.nat.
Definition  a49 := 1%nat : Preamble.nat.
Definition  a495 := 1%nat : Preamble.nat.
Definition  a497 := 1%nat : Preamble.nat.
Definition  a5 := 1%nat : Preamble.nat.
Definition  a50 := 1%nat : Preamble.nat.
Definition  a501 := 1%nat : Preamble.nat.
Definition  a505 := 1%nat : Preamble.nat.
Definition  a506 := 1%nat : Preamble.nat.
Definition  a508 := 1%nat : Preamble.nat.
Definition  a5088 := 1%nat : Preamble.nat.
Definition  a5114 := 1%nat : Preamble.nat.
Definition  a5115 := 1%nat : Preamble.nat.
Definition  a5152 := 1%nat : Preamble.nat.
Definition  a5154 := 1%nat : Preamble.nat.
Definition  a5161 := 1%nat : Preamble.nat.
Definition  a5167 := 1%nat : Preamble.nat.
Definition  a5170 := 1%nat : Preamble.nat.
Definition  a5171 := 1%nat : Preamble.nat.
Definition  a5173 := 1%nat : Preamble.nat.
Definition  a5175 := 1%nat : Preamble.nat.
Definition  a5180 := 1%nat : Preamble.nat.
Definition  a5181 := 1%nat : Preamble.nat.
Definition  a5183 := 1%nat : Preamble.nat.
Definition  a5184 := 1%nat : Preamble.nat.
Definition  a5188 := 1%nat : Preamble.nat.
Definition  a5190 := 1%nat : Preamble.nat.
Definition  a5196 := 1%nat : Preamble.nat.
Definition  a52 := 1%nat : Preamble.nat.
Definition  a5201 := 1%nat : Preamble.nat.
Definition  a5204 := 1%nat : Preamble.nat.
Definition  a5207 := 1%nat : Preamble.nat.
Definition  a5210 := 1%nat : Preamble.nat.
Definition  a5211 := 1%nat : Preamble.nat.
Definition  a5213 := 1%nat : Preamble.nat.
Definition  a5216 := 1%nat : Preamble.nat.
Definition  a5219 := 1%nat : Preamble.nat.
Definition  a52192787 := 1%nat : Preamble.nat.
Definition  a5220 := 1%nat : Preamble.nat.
Definition  a5221 := 1%nat : Preamble.nat.
Definition  a5224 := 1%nat : Preamble.nat.
Definition  a5227 := 1%nat : Preamble.nat.
Definition  a5229 := 1%nat : Preamble.nat.
Definition  a5239 := 1%nat : Preamble.nat.
Definition  a5244 := 1%nat : Preamble.nat.
Definition  a5255 := 1%nat : Preamble.nat.
Definition  a5256 := 1%nat : Preamble.nat.
Definition  a526 := 1%nat : Preamble.nat.
Definition  a5266 := 1%nat : Preamble.nat.
Definition  a5269 := 1%nat : Preamble.nat.
Definition  a5278 := 1%nat : Preamble.nat.
Definition  a5279 := 1%nat : Preamble.nat.
Definition  a5289 := 1%nat : Preamble.nat.
Definition  a5292 := 1%nat : Preamble.nat.
Definition  a5301 := 1%nat : Preamble.nat.
Definition  a5303 := 1%nat : Preamble.nat.
Definition  a5312 := 1%nat : Preamble.nat.
Definition  a5331 := 1%nat : Preamble.nat.
Definition  a5336 := 1%nat : Preamble.nat.
Definition  a5342 := 1%nat : Preamble.nat.
Definition  a5344 := 1%nat : Preamble.nat.
Definition  a5347 := 1%nat : Preamble.nat.
Definition  a5348 := 1%nat : Preamble.nat.
Definition  a5350 := 1%nat : Preamble.nat.
Definition  a5354 := 1%nat : Preamble.nat.
Definition  a5360 := 1%nat : Preamble.nat.
Definition  a5362 := 1%nat : Preamble.nat.
Definition  a5365 := 1%nat : Preamble.nat.
Definition  a5366 := 1%nat : Preamble.nat.
Definition  a5368 := 1%nat : Preamble.nat.
Definition  a5369 := 1%nat : Preamble.nat.
Definition  a5370 := 1%nat : Preamble.nat.
Definition  a5374 := 1%nat : Preamble.nat.
Definition  a5375 := 1%nat : Preamble.nat.
Definition  a5377 := 1%nat : Preamble.nat.
Definition  a538 := 1%nat : Preamble.nat.
Definition  a5380 := 1%nat : Preamble.nat.
Definition  a5392 := 1%nat : Preamble.nat.
Definition  a5394 := 1%nat : Preamble.nat.
Definition  a5402 := 1%nat : Preamble.nat.
Definition  a5404 := 1%nat : Preamble.nat.
Definition  a541 := 1%nat : Preamble.nat.
Definition  a5412 := 1%nat : Preamble.nat.
Definition  a5414 := 1%nat : Preamble.nat.
Definition  a543 := 1%nat : Preamble.nat.
Definition  a5433 := 1%nat : Preamble.nat.
Definition  a5448 := 1%nat : Preamble.nat.
Definition  a558 := 1%nat : Preamble.nat.
Definition  a583 := 1%nat : Preamble.nat.
Definition  a59 := 1%nat : Preamble.nat.
Definition  a593 := 1%nat : Preamble.nat.
Definition  a598 := 1%nat : Preamble.nat.
Definition  a6 := 1%nat : Preamble.nat.
Definition  a60 := 1%nat : Preamble.nat.
Definition  a601 := 1%nat : Preamble.nat.
Definition  a603 := 1%nat : Preamble.nat.
Definition  a608 := 1%nat : Preamble.nat.
Definition  a61 := 1%nat : Preamble.nat.
Definition  a610 := 1%nat : Preamble.nat.
Definition  a619 := 1%nat : Preamble.nat.
Definition  a624 := 1%nat : Preamble.nat.
Definition  a628 := 1%nat : Preamble.nat.
Definition  a63 := 1%nat : Preamble.nat.
Definition  a633 := 1%nat : Preamble.nat.
Definition  a634 := 1%nat : Preamble.nat.
Definition  a65 := 1%nat : Preamble.nat.
Definition  a66 := 1%nat : Preamble.nat.
Definition  a665 := 1%nat : Preamble.nat.
Definition  a67 := 1%nat : Preamble.nat.
Definition  a675 := 1%nat : Preamble.nat.
Definition  a679 := 1%nat : Preamble.nat.
Definition  a68 := 1%nat : Preamble.nat.
Definition  a682 := 1%nat : Preamble.nat.
Definition  a684 := 1%nat : Preamble.nat.
Definition  a688 := 1%nat : Preamble.nat.
Definition  a69 := 1%nat : Preamble.nat.
Definition  a692 := 1%nat : Preamble.nat.
Definition  a694 := 1%nat : Preamble.nat.
Definition  a697 := 1%nat : Preamble.nat.
Definition  a7 := 1%nat : Preamble.nat.
Definition  a701 := 1%nat : Preamble.nat.
Definition  a702 := 1%nat : Preamble.nat.
Definition  a71 := 1%nat : Preamble.nat.
Definition  a72 := 1%nat : Preamble.nat.
Definition  a73 := 1%nat : Preamble.nat.
Definition  a733 := 1%nat : Preamble.nat.
Definition  a74 := 1%nat : Preamble.nat.
Definition  a743 := 1%nat : Preamble.nat.
Definition  a747 := 1%nat : Preamble.nat.
Definition  a75 := 1%nat : Preamble.nat.
Definition  a750 := 1%nat : Preamble.nat.
Definition  a752 := 1%nat : Preamble.nat.
Definition  a756 := 1%nat : Preamble.nat.
Definition  a76 := 1%nat : Preamble.nat.
Definition  a760 := 1%nat : Preamble.nat.
Definition  a764 := 1%nat : Preamble.nat.
Definition  a767 := 1%nat : Preamble.nat.
Definition  a771 := 1%nat : Preamble.nat.
Definition  a772 := 1%nat : Preamble.nat.
Definition  a776 := 1%nat : Preamble.nat.
Definition  a78 := 1%nat : Preamble.nat.
Definition  a781 := 1%nat : Preamble.nat.
Definition  a784 := 1%nat : Preamble.nat.
Definition  a788 := 1%nat : Preamble.nat.
Definition  a789 := 1%nat : Preamble.nat.
Definition  a79 := 1%nat : Preamble.nat.
Definition  a791 := 1%nat : Preamble.nat.
Definition  a8 := 1%nat : Preamble.nat.
Definition  a80 := 1%nat : Preamble.nat.
Definition  a802 := 1%nat : Preamble.nat.
Definition  a806 := 1%nat : Preamble.nat.
Definition  a808 := 1%nat : Preamble.nat.
Definition  a809 := 1%nat : Preamble.nat.
Definition  a81 := 1%nat : Preamble.nat.
Definition  a810 := 1%nat : Preamble.nat.
Definition  a814 := 1%nat : Preamble.nat.
Definition  a819 := 1%nat : Preamble.nat.
Definition  a82 := 1%nat : Preamble.nat.
Definition  a822 := 1%nat : Preamble.nat.
Definition  a823 := 1%nat : Preamble.nat.
Definition  a829 := 1%nat : Preamble.nat.
Definition  a83 := 1%nat : Preamble.nat.
Definition  a834 := 1%nat : Preamble.nat.
Definition  a840 := 1%nat : Preamble.nat.
Definition  a844 := 1%nat : Preamble.nat.
Definition  a845 := 1%nat : Preamble.nat.
Definition  a86 := 1%nat : Preamble.nat.
Definition  a87 := 1%nat : Preamble.nat.
Definition  a88 := 1%nat : Preamble.nat.
Definition  a882 := 1%nat : Preamble.nat.
Definition  a89 := 1%nat : Preamble.nat.
Definition  a892 := 1%nat : Preamble.nat.
Definition  a898 := 1%nat : Preamble.nat.
Definition  a9 := 1%nat : Preamble.nat.
Definition  a90 := 1%nat : Preamble.nat.
Definition  a900 := 1%nat : Preamble.nat.
Definition  a901 := 1%nat : Preamble.nat.
Definition  a902 := 1%nat : Preamble.nat.
Definition  a903 := 1%nat : Preamble.nat.
Definition  a904 := 1%nat : Preamble.nat.
Definition  a906 := 1%nat : Preamble.nat.
Definition  a91 := 1%nat : Preamble.nat.
Definition  a910 := 1%nat : Preamble.nat.
Definition  a912 := 1%nat : Preamble.nat.
Definition  a916 := 1%nat : Preamble.nat.
Definition  a918 := 1%nat : Preamble.nat.
Definition  a92 := 1%nat : Preamble.nat.
Definition  a921 := 1%nat : Preamble.nat.
Definition  a924 := 1%nat : Preamble.nat.
Definition  a925 := 1%nat : Preamble.nat.
Definition  a929 := 1%nat : Preamble.nat.
Definition  a935 := 1%nat : Preamble.nat.
Definition  a936 := 1%nat : Preamble.nat.
Definition  a937 := 1%nat : Preamble.nat.
Definition  a938 := 1%nat : Preamble.nat.
Definition  a939 := 1%nat : Preamble.nat.
Definition  a94 := 1%nat : Preamble.nat.
Definition  a940 := 1%nat : Preamble.nat.
Definition  a942 := 1%nat : Preamble.nat.
Definition  a945 := 1%nat : Preamble.nat.
Definition  a948 := 1%nat : Preamble.nat.
Definition  a949 := 1%nat : Preamble.nat.
Definition  a953 := 1%nat : Preamble.nat.
Definition  a959 := 1%nat : Preamble.nat.
Definition  a96 := 1%nat : Preamble.nat.
Definition  a960 := 1%nat : Preamble.nat.
Definition  a961 := 1%nat : Preamble.nat.
Definition  a962 := 1%nat : Preamble.nat.
Definition  a963 := 1%nat : Preamble.nat.
Definition  a964 := 1%nat : Preamble.nat.
Definition  a966 := 1%nat : Preamble.nat.
Definition  a97 := 1%nat : Preamble.nat.
Definition  a976 := 1%nat : Preamble.nat.
Definition  a98 := 1%nat : Preamble.nat.
Definition  a987 := 1%nat : Preamble.nat.
Definition  a99 := 1%nat : Preamble.nat.

(*
for x in `grep -P -e"(\d+)" -o ~/experiments/UniMath/UniMath/Introspector/Unimathcore_refl2_coq.v |sort -u`; do echo "Definition  a$x := 1%nat : Preamble.nat."; done
 *)

Definition aa11 := (Id Foundations).
Definition aa12  := (Id UniMath).
Definition aa13 := ( mycons aa12 mynil).
Definition aa1 := (mycons aa11 aa13).
Definition ufile := (file (mycons2 UniMath (mycons2 Foundations (mycons2 Preamble mynil2)))).
Definition test124 := ((v3((control)(attrs)(expr(VernacSynterp(VernacRequire((AdExport))((((v3(Ser_Qualid(DirPath(aa1))(Id Init)))(loc(((fname(InFile(dirpath)ufile))
                                                                                                                                          (line_nb 12)
                                                                                                                                          (bol_pos a415)
                                                                                                                                          (line_nb_last 12)
                                                                                                                                          (bol_pos_last a415)(bp a430)(ep a454)))))ImportAll)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 12)(bol_pos a415)(line_nb_last 12)(bol_pos_last a415)(bp a415)(ep a455))))).

Definition test12UU :=((v3((control)(attrs)(expr(
                                               VernacSynPure(VernacDefinition
                                                               (NoDischarge_Definition)
                                                               (((
                                                                    v2(
                                                                        Name(Id2 UU))
                                                                  )(loc(((fname(InFile(dirpath)ufile))(line_nb 16)(bol_pos a484)(line_nb_last 16)(bol_pos_last a484)(bp a495)(ep a497))))))
                                                               (DefineBody(
                                                                    (v2(
                                                                         CSort(UAnonymous(rigid true))
                                                                    ))
                                                                      (loc(((fname(InFile(dirpath)ufile))(line_nb 16)(bol_pos a484)(line_nb_last 16)(bol_pos_last a484)(bp a501)(ep a505)))))
                                                               )
                                                 )
                       ))))(loc(((fname(InFile(dirpath)ufile))
                                   (line_nb 16)(bol_pos a484)(line_nb_last 16)(bol_pos_last a484)(bp a484)(ep a506))))
                      ).

(* ((v((control)(attrs)(expr(VernacSynPure(VernacIdentityCoercion((v(Id fromUUtoType))(loc(((fname(InFile(dirpath)ufile))(line_nb 18)(bol_pos 508)(line_nb_last 18)(bol_pos_last 508)(bp 526)(ep 538)))))(RefClass((v(AN((v(Ser_Qualid(DirPath)(Id UU)))(loc(((fname(InFile(dirpath)ufile))(line_nb 18)(bol_pos 508)(line_nb_last 18)(bol_pos_last 508)(bp 541)(ep 543)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 18)(bol_pos 508)(line_nb_last 18)(bol_pos_last 508)(bp 541)(ep 543))))))SortClass)))))(loc(((fname(InFile(dirpath)ufile))(line_nb 18)(bol_pos 508)(line_nb_last 18)(bol_pos_last 508)(bp 508)(ep 558))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacInductive Inductive_kw((((NoCoercion(((v(Id empty))(loc(((fname(InFile(dirpath)ufile))(line_nb 22)(bol_pos 583)(line_nb_last 22)(bol_pos_last 583)(bp 593)(ep 598)))))))()(((v(CRef((v(Ser_Qualid(DirPath)(Id UU)))(loc(((fname(InFile(dirpath)ufile))(line_nb 22)(bol_pos 583)(line_nb_last 22)(bol_pos_last 583)(bp 601)(ep 603)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 22)(bol_pos 583)(line_nb_last 22)(bol_pos_last 583)(bp 601)(ep 603))))))(Constructors)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 22)(bol_pos 583)(line_nb_last 22)(bol_pos_last 583)(bp 583)(ep 608))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v ∅)(loc(((fname(InFile(dirpath)ufile))(line_nb 24)(bol_pos 610)(line_nb_last 24)(bol_pos_last 610)(bp 619)(ep 624))))))(ntn_decl_interp((v(CRef((v(Ser_Qualid(DirPath)(Id empty)))(loc(((fname(InFile(dirpath)ufile))(line_nb 24)(bol_pos 610)(line_nb_last 24)(bol_pos_last 610)(bp 628)(ep 633)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 24)(bol_pos 610)(line_nb_last 24)(bol_pos_last 610)(bp 628)(ep 633))))))(ntn_decl_scope)(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 24)(bol_pos 610)(line_nb_last 24)(bol_pos_last 610)(bp 610)(ep 634))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacInductive Inductive_kw((((NoCoercion(((v(Id unit))(loc(((fname(InFile(dirpath)ufile))(line_nb 28)(bol_pos 665)(line_nb_last 28)(bol_pos_last 665)(bp 675)(ep 679)))))))()(((v(CRef((v(Ser_Qualid(DirPath)(Id UU)))(loc(((fname(InFile(dirpath)ufile))(line_nb 28)(bol_pos 665)(line_nb_last 28)(bol_pos_last 665)(bp 682)(ep 684)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 28)(bol_pos 665)(line_nb_last 28)(bol_pos_last 665)(bp 682)(ep 684))))))(Constructors(((NoCoercion NoInstance)(((v(Id tt))(loc(((fname(InFile(dirpath)ufile))(line_nb 29)(bol_pos 688)(line_nb_last 29)(bol_pos_last 688)(bp 692)(ep 694)))))((v(CRef((v(Ser_Qualid(DirPath)(Id unit)))(loc(((fname(InFile(dirpath)ufile))(line_nb 29)(bol_pos 688)(line_nb_last 29)(bol_pos_last 688)(bp 697)(ep 701)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 29)(bol_pos 688)(line_nb_last 29)(bol_pos_last 688)(bp 697)(ep 701)))))))))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 28)(bol_pos 665)(line_nb_last 29)(bol_pos_last 688)(bp 665)(ep 702))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacInductive Inductive_kw((((NoCoercion(((v(Id bool))(loc(((fname(InFile(dirpath)ufile))(line_nb 33)(bol_pos 733)(line_nb_last 33)(bol_pos_last 733)(bp 743)(ep 747)))))))()(((v(CRef((v(Ser_Qualid(DirPath)(Id UU)))(loc(((fname(InFile(dirpath)ufile))(line_nb 33)(bol_pos 733)(line_nb_last 33)(bol_pos_last 733)(bp 750)(ep 752)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 33)(bol_pos 733)(line_nb_last 33)(bol_pos_last 733)(bp 750)(ep 752))))))(Constructors(((NoCoercion NoInstance)(((v(Id true))(loc(((fname(InFile(dirpath)ufile))(line_nb 34)(bol_pos 756)(line_nb_last 34)(bol_pos_last 756)(bp 760)(ep 764)))))((v(CRef((v(Ser_Qualid(DirPath)(Id bool)))(loc(((fname(InFile(dirpath)ufile))(line_nb 34)(bol_pos 756)(line_nb_last 34)(bol_pos_last 756)(bp 767)(ep 771)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 34)(bol_pos 756)(line_nb_last 34)(bol_pos_last 756)(bp 767)(ep 771)))))))((NoCoercion NoInstance)(((v(Id false))(loc(((fname(InFile(dirpath)ufile))(line_nb 35)(bol_pos 772)(line_nb_last 35)(bol_pos_last 772)(bp 776)(ep 781)))))((v(CRef((v(Ser_Qualid(DirPath)(Id bool)))(loc(((fname(InFile(dirpath)ufile))(line_nb 35)(bol_pos 772)(line_nb_last 35)(bol_pos_last 772)(bp 784)(ep 788)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 35)(bol_pos 772)(line_nb_last 35)(bol_pos_last 772)(bp 784)(ep 788)))))))))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 33)(bol_pos 733)(line_nb_last 35)(bol_pos_last 772)(bp 733)(ep 789))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacDefinition(NoDischarge Definition)(((v(Name(Id negb)))(loc(((fname(InFile(dirpath)ufile))(line_nb 37)(bol_pos 791)(line_nb_last 37)(bol_pos_last 791)(bp 802)(ep 806))))))(DefineBody((CLocalAssum(((v(Name(Id b)))(loc(((fname(InFile(dirpath)ufile))(line_nb 37)(bol_pos 791)(line_nb_last 37)(bol_pos_last 791)(bp 808)(ep 809))))))(Default Explicit)((v(CRef((v(Ser_Qualid(DirPath)(Id bool)))(loc(((fname(InFile(dirpath)ufile))(line_nb 37)(bol_pos 791)(line_nb_last 37)(bol_pos_last 791)(bp 810)(ep 814)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 37)(bol_pos 791)(line_nb_last 37)(bol_pos_last 791)(bp 810)(ep 814)))))))((v(CIf((v(CRef((v(Ser_Qualid(DirPath)(Id b)))(loc(((fname(InFile(dirpath)ufile))(line_nb 37)(bol_pos 791)(line_nb_last 37)(bol_pos_last 791)(bp 822)(ep 823)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 37)(bol_pos 791)(line_nb_last 37)(bol_pos_last 791)(bp 822)(ep 823)))))()((v(CRef((v(Ser_Qualid(DirPath)(Id false)))(loc(((fname(InFile(dirpath)ufile))(line_nb 37)(bol_pos 791)(line_nb_last 37)(bol_pos_last 791)(bp 829)(ep 834)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 37)(bol_pos 791)(line_nb_last 37)(bol_pos_last 791)(bp 829)(ep 834)))))((v(CRef((v(Ser_Qualid(DirPath)(Id true)))(loc(((fname(InFile(dirpath)ufile))(line_nb 37)(bol_pos 791)(line_nb_last 37)(bol_pos_last 791)(bp 840)(ep 844)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 37)(bol_pos 791)(line_nb_last 37)(bol_pos_last 791)(bp 840)(ep 844)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 37)(bol_pos 791)(line_nb_last 37)(bol_pos_last 791)(bp 819)(ep 844)))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 37)(bol_pos 791)(line_nb_last 37)(bol_pos_last 791)(bp 791)(ep 845))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacInductive Inductive_kw((((NoCoercion(((v(Id coprod))(loc(((fname(InFile(dirpath)ufile))(line_nb 41)(bol_pos 882)(line_nb_last 41)(bol_pos_last 882)(bp 892)(ep 898)))))))(((CLocalAssum(((v(Name(Id A)))(loc(((fname(InFile(dirpath)ufile))(line_nb 41)(bol_pos 882)(line_nb_last 41)(bol_pos_last 882)(bp 900)(ep 901)))))((v(Name(Id B)))(loc(((fname(InFile(dirpath)ufile))(line_nb 41)(bol_pos 882)(line_nb_last 41)(bol_pos_last 882)(bp 902)(ep 903))))))(Default Explicit)((v(CRef((v(Ser_Qualid(DirPath)(Id UU)))(loc(((fname(InFile(dirpath)ufile))(line_nb 41)(bol_pos 882)(line_nb_last 41)(bol_pos_last 882)(bp 904)(ep 906)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 41)(bol_pos 882)(line_nb_last 41)(bol_pos_last 882)(bp 904)(ep 906))))))))(((v(CRef((v(Ser_Qualid(DirPath)(Id UU)))(loc(((fname(InFile(dirpath)ufile))(line_nb 41)(bol_pos 882)(line_nb_last 41)(bol_pos_last 882)(bp 910)(ep 912)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 41)(bol_pos 882)(line_nb_last 41)(bol_pos_last 882)(bp 910)(ep 912))))))(Constructors(((NoCoercion NoInstance)(((v(Id ii1))(loc(((fname(InFile(dirpath)ufile))(line_nb 42)(bol_pos 916)(line_nb_last 42)(bol_pos_last 916)(bp 918)(ep 921)))))((v(CNotation(InConstrEntry"_ -> _")((((v(CRef((v(Ser_Qualid(DirPath)(Id A)))(loc(((fname(InFile(dirpath)ufile))(line_nb 42)(bol_pos 916)(line_nb_last 42)(bol_pos_last 916)(bp 924)(ep 925)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 42)(bol_pos 916)(line_nb_last 42)(bol_pos_last 916)(bp 924)(ep 925)))))((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id coprod)))(loc(((fname(InFile(dirpath)ufile))(line_nb 42)(bol_pos 916)(line_nb_last 42)(bol_pos_last 916)(bp 929)(ep 935)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 42)(bol_pos 916)(line_nb_last 42)(bol_pos_last 916)(bp 929)(ep 935)))))((((v(CRef((v(Ser_Qualid(DirPath)(Id A)))(loc(((fname(InFile(dirpath)ufile))(line_nb 42)(bol_pos 916)(line_nb_last 42)(bol_pos_last 916)(bp 936)(ep 937)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 42)(bol_pos 916)(line_nb_last 42)(bol_pos_last 916)(bp 936)(ep 937))))))(((v(CRef((v(Ser_Qualid(DirPath)(Id B)))(loc(((fname(InFile(dirpath)ufile))(line_nb 42)(bol_pos 916)(line_nb_last 42)(bol_pos_last 916)(bp 938)(ep 939)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 42)(bol_pos 916)(line_nb_last 42)(bol_pos_last 916)(bp 938)(ep 939)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 42)(bol_pos 916)(line_nb_last 42)(bol_pos_last 916)(bp 929)(ep 939)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 42)(bol_pos 916)(line_nb_last 42)(bol_pos_last 916)(bp 924)(ep 939)))))))((NoCoercion NoInstance)(((v(Id ii2))(loc(((fname(InFile(dirpath)ufile))(line_nb 43)(bol_pos 940)(line_nb_last 43)(bol_pos_last 940)(bp 942)(ep 945)))))((v(CNotation(InConstrEntry"_ -> _")((((v(CRef((v(Ser_Qualid(DirPath)(Id B)))(loc(((fname(InFile(dirpath)ufile))(line_nb 43)(bol_pos 940)(line_nb_last 43)(bol_pos_last 940)(bp 948)(ep 949)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 43)(bol_pos 940)(line_nb_last 43)(bol_pos_last 940)(bp 948)(ep 949)))))((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id coprod)))(loc(((fname(InFile(dirpath)ufile))(line_nb 43)(bol_pos 940)(line_nb_last 43)(bol_pos_last 940)(bp 953)(ep 959)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 43)(bol_pos 940)(line_nb_last 43)(bol_pos_last 940)(bp 953)(ep 959)))))((((v(CRef((v(Ser_Qualid(DirPath)(Id A)))(loc(((fname(InFile(dirpath)ufile))(line_nb 43)(bol_pos 940)(line_nb_last 43)(bol_pos_last 940)(bp 960)(ep 961)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 43)(bol_pos 940)(line_nb_last 43)(bol_pos_last 940)(bp 960)(ep 961))))))(((v(CRef((v(Ser_Qualid(DirPath)(Id B)))(loc(((fname(InFile(dirpath)ufile))(line_nb 43)(bol_pos 940)(line_nb_last 43)(bol_pos_last 940)(bp 962)(ep 963)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 43)(bol_pos 940)(line_nb_last 43)(bol_pos_last 940)(bp 962)(ep 963)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 43)(bol_pos 940)(line_nb_last 43)(bol_pos_last 940)(bp 953)(ep 963)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 43)(bol_pos 940)(line_nb_last 43)(bol_pos_last 940)(bp 948)(ep 963)))))))))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 41)(bol_pos 882)(line_nb_last 43)(bol_pos_last 940)(bp 882)(ep 964))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacArguments((v(AN((v(Ser_Qualid(DirPath)(Id coprod_rect)))(loc(((fname(InFile(dirpath)ufile))(line_nb 45)(bol_pos 966)(line_nb_last 45)(bol_pos_last 966)(bp 976)(ep 987)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 45)(bol_pos 966)(line_nb_last 45)(bol_pos_last 966)(bp 976)(ep 987)))))((RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status MaxImplicit)))(RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status MaxImplicit)))(RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status Explicit)))(RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status Explicit)))(RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status Explicit)))(RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status Explicit)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 45)(bol_pos 966)(line_nb_last 45)(bol_pos_last 966)(bp 966)(ep 1002))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacArguments((v(AN((v(Ser_Qualid(DirPath)(Id ii1)))(loc(((fname(InFile(dirpath)ufile))(line_nb 46)(bol_pos 1003)(line_nb_last 46)(bol_pos_last 1003)(bp 1013)(ep 1016)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 46)(bol_pos 1003)(line_nb_last 46)(bol_pos_last 1003)(bp 1013)(ep 1016)))))((RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status MaxImplicit)))(RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status MaxImplicit)))(RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status Explicit)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 46)(bol_pos 1003)(line_nb_last 46)(bol_pos_last 1003)(bp 1003)(ep 1025))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacArguments((v(AN((v(Ser_Qualid(DirPath)(Id ii2)))(loc(((fname(InFile(dirpath)ufile))(line_nb 47)(bol_pos 1026)(line_nb_last 47)(bol_pos_last 1026)(bp 1036)(ep 1039)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 47)(bol_pos 1026)(line_nb_last 47)(bol_pos_last 1026)(bp 1036)(ep 1039)))))((RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status MaxImplicit)))(RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status MaxImplicit)))(RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status Explicit)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 47)(bol_pos 1026)(line_nb_last 47)(bol_pos_last 1026)(bp 1026)(ep 1048))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacSyntacticDefinition((v(Id inl))(loc(((fname(InFile(dirpath)ufile))(line_nb 49)(bol_pos 1050)(line_nb_last 49)(bol_pos_last 1050)(bp 1059)(ep 1062)))))(((v(CRef((v(Ser_Qualid(DirPath)(Id ii1)))(loc(((fname(InFile(dirpath)ufile))(line_nb 49)(bol_pos 1050)(line_nb_last 49)(bol_pos_last 1050)(bp 1066)(ep 1069)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 49)(bol_pos 1050)(line_nb_last 49)(bol_pos_last 1050)(bp 1066)(ep 1069)))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 49)(bol_pos 1050)(line_nb_last 49)(bol_pos_last 1050)(bp 1050)(ep 1070))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacSyntacticDefinition((v(Id inr))(loc(((fname(InFile(dirpath)ufile))(line_nb 50)(bol_pos 1127)(line_nb_last 50)(bol_pos_last 1127)(bp 1136)(ep 1139)))))(((v(CRef((v(Ser_Qualid(DirPath)(Id ii2)))(loc(((fname(InFile(dirpath)ufile))(line_nb 50)(bol_pos 1127)(line_nb_last 50)(bol_pos_last 1127)(bp 1143)(ep 1146)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 50)(bol_pos 1127)(line_nb_last 50)(bol_pos_last 1127)(bp 1143)(ep 1146)))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 50)(bol_pos 1127)(line_nb_last 50)(bol_pos_last 1127)(bp 1127)(ep 1147))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v"X ⨿ Y")(loc(((fname(InFile(dirpath)ufile))(line_nb 52)(bol_pos 1205)(line_nb_last 52)(bol_pos_last 1205)(bp 1214)(ep 1223))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id coprod)))(loc(((fname(InFile(dirpath)ufile))(line_nb 52)(bol_pos 1205)(line_nb_last 52)(bol_pos_last 1205)(bp 1228)(ep 1234)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 52)(bol_pos 1205)(line_nb_last 52)(bol_pos_last 1205)(bp 1228)(ep 1234)))))((((v(CRef((v(Ser_Qualid(DirPath)(Id X)))(loc(((fname(InFile(dirpath)ufile))(line_nb 52)(bol_pos 1205)(line_nb_last 52)(bol_pos_last 1205)(bp 1235)(ep 1236)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 52)(bol_pos 1205)(line_nb_last 52)(bol_pos_last 1205)(bp 1235)(ep 1236))))))(((v(CRef((v(Ser_Qualid(DirPath)(Id Y)))(loc(((fname(InFile(dirpath)ufile))(line_nb 52)(bol_pos 1205)(line_nb_last 52)(bol_pos_last 1205)(bp 1237)(ep 1238)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 52)(bol_pos 1205)(line_nb_last 52)(bol_pos_last 1205)(bp 1237)(ep 1238)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 52)(bol_pos 1205)(line_nb_last 52)(bol_pos_last 1205)(bp 1228)(ep 1238))))))(ntn_decl_scope)(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 52)(bol_pos 1205)(line_nb_last 52)(bol_pos_last 1205)(bp 1205)(ep 1240))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacInductive Inductive_kw((((NoCoercion(((v(Id nat))(loc(((fname(InFile(dirpath)ufile))(line_nb 59)(bol_pos 1382)(line_nb_last 59)(bol_pos_last 1382)(bp 1392)(ep 1395)))))))()(((v(CRef((v(Ser_Qualid(DirPath)(Id UU)))(loc(((fname(InFile(dirpath)ufile))(line_nb 59)(bol_pos 1382)(line_nb_last 59)(bol_pos_last 1382)(bp 1398)(ep 1400)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 59)(bol_pos 1382)(line_nb_last 59)(bol_pos_last 1382)(bp 1398)(ep 1400))))))(Constructors(((NoCoercion NoInstance)(((v(Id O))(loc(((fname(InFile(dirpath)ufile))(line_nb 60)(bol_pos 1404)(line_nb_last 60)(bol_pos_last 1404)(bp 1408)(ep 1409)))))((v(CRef((v(Ser_Qualid(DirPath)(Id nat)))(loc(((fname(InFile(dirpath)ufile))(line_nb 60)(bol_pos 1404)(line_nb_last 60)(bol_pos_last 1404)(bp 1412)(ep 1415)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 60)(bol_pos 1404)(line_nb_last 60)(bol_pos_last 1404)(bp 1412)(ep 1415)))))))((NoCoercion NoInstance)(((v(Id S))(loc(((fname(InFile(dirpath)ufile))(line_nb 61)(bol_pos 1416)(line_nb_last 61)(bol_pos_last 1416)(bp 1420)(ep 1421)))))((v(CNotation(InConstrEntry"_ -> _")((((v(CRef((v(Ser_Qualid(DirPath)(Id nat)))(loc(((fname(InFile(dirpath)ufile))(line_nb 61)(bol_pos 1416)(line_nb_last 61)(bol_pos_last 1416)(bp 1424)(ep 1427)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 61)(bol_pos 1416)(line_nb_last 61)(bol_pos_last 1416)(bp 1424)(ep 1427)))))((v(CRef((v(Ser_Qualid(DirPath)(Id nat)))(loc(((fname(InFile(dirpath)ufile))(line_nb 61)(bol_pos 1416)(line_nb_last 61)(bol_pos_last 1416)(bp 1431)(ep 1434)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 61)(bol_pos 1416)(line_nb_last 61)(bol_pos_last 1416)(bp 1431)(ep 1434)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 61)(bol_pos 1416)(line_nb_last 61)(bol_pos_last 1416)(bp 1424)(ep 1434)))))))))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 59)(bol_pos 1382)(line_nb_last 61)(bol_pos_last 1416)(bp 1382)(ep 1435))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacDefinition(NoDischarge Definition)(((v(Name(Id succ)))(loc(((fname(InFile(dirpath)ufile))(line_nb 63)(bol_pos 1437)(line_nb_last 63)(bol_pos_last 1437)(bp 1448)(ep 1452))))))(DefineBody((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 63)(bol_pos 1437)(line_nb_last 63)(bol_pos_last 1437)(bp 1456)(ep 1457)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 63)(bol_pos 1437)(line_nb_last 63)(bol_pos_last 1437)(bp 1456)(ep 1457)))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 63)(bol_pos 1437)(line_nb_last 63)(bol_pos_last 1437)(bp 1437)(ep 1458))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacDeclareScope nat_scope)))))(loc(((fname(InFile(dirpath)ufile))(line_nb 65)(bol_pos 1460)(line_nb_last 65)(bol_pos_last 1460)(bp 1460)(ep 1484))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacDelimiters nat_scope(nat))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 66)(bol_pos 1485)(line_nb_last 66)(bol_pos_last 1485)(bp 1485)(ep 1518))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacBindScope nat_scope((RefClass((v(AN((v(Ser_Qualid(DirPath)(Id nat)))(loc(((fname(InFile(dirpath)ufile))(line_nb 67)(bol_pos 1519)(line_nb_last 67)(bol_pos_last 1519)(bp 1545)(ep 1548)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 67)(bol_pos 1519)(line_nb_last 67)(bol_pos_last 1519)(bp 1545)(ep 1548))))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 67)(bol_pos 1519)(line_nb_last 67)(bol_pos_last 1519)(bp 1519)(ep 1549))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacArguments((v(AN((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 68)(bol_pos 1550)(line_nb_last 68)(bol_pos_last 1550)(bp 1560)(ep 1561)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 68)(bol_pos 1550)(line_nb_last 68)(bol_pos_last 1550)(bp 1560)(ep 1561)))))((RealArg((name Anonymous)(recarg_like false)(notation_scope(((v nat)(loc(((fname(InFile(dirpath)ufile))(line_nb 68)(bol_pos 1550)(line_nb_last 68)(bol_pos_last 1550)(bp 1562)(ep 1567)))))))(implicit_status Explicit)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 68)(bol_pos 1550)(line_nb_last 68)(bol_pos_last 1550)(bp 1550)(ep 1568))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacOpenCloseScope true nat_scope)))))(loc(((fname(InFile(dirpath)ufile))(line_nb 69)(bol_pos 1569)(line_nb_last 69)(bol_pos_last 1569)(bp 1569)(ep 1590))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacFixpoint NoDischarge(((fname((v(Id add))(loc(((fname(InFile(dirpath)ufile))(line_nb 71)(bol_pos 1592)(line_nb_last 71)(bol_pos_last 1592)(bp 1601)(ep 1604))))))(univs)(rec_order)(binders((CLocalAssum(((v(Name(Id n)))(loc(((fname(InFile(dirpath)ufile))(line_nb 71)(bol_pos 1592)(line_nb_last 71)(bol_pos_last 1592)(bp 1605)(ep 1606))))))(Default Explicit)((v(CHoleIntroAnonymous))(loc(((fname(InFile(dirpath)ufile))(line_nb 71)(bol_pos 1592)(line_nb_last 71)(bol_pos_last 1592)(bp 1605)(ep 1606))))))(CLocalAssum(((v(Name(Id m)))(loc(((fname(InFile(dirpath)ufile))(line_nb 71)(bol_pos 1592)(line_nb_last 71)(bol_pos_last 1592)(bp 1607)(ep 1608))))))(Default Explicit)((v(CHoleIntroAnonymous))(loc(((fname(InFile(dirpath)ufile))(line_nb 71)(bol_pos 1592)(line_nb_last 71)(bol_pos_last 1592)(bp 1607)(ep 1608))))))))(rtype((v(CHoleIntroAnonymous))(loc(((fname(InFile(dirpath)ufile))(line_nb 71)(bol_pos 1592)(line_nb_last 71)(bol_pos_last 1592)(bp 1608)(ep 1608))))))(body_def(((v(CCases RegularStyle((((v(CRef((v(Ser_Qualid(DirPath)(Id n)))(loc(((fname(InFile(dirpath)ufile))(line_nb 72)(bol_pos 1612)(line_nb_last 72)(bol_pos_last 1612)(bp 1620)(ep 1621)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 72)(bol_pos 1612)(line_nb_last 72)(bol_pos_last 1612)(bp 1620)(ep 1621)))))))(((v(((((v(CPatAtom(((v(Ser_Qualid(DirPath)(Id O)))(loc(((fname(InFile(dirpath)ufile))(line_nb 73)(bol_pos 1627)(line_nb_last 73)(bol_pos_last 1627)(bp 1631)(ep 1632))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 73)(bol_pos 1627)(line_nb_last 73)(bol_pos_last 1627)(bp 1631)(ep 1632)))))))((v(CRef((v(Ser_Qualid(DirPath)(Id m)))(loc(((fname(InFile(dirpath)ufile))(line_nb 73)(bol_pos 1627)(line_nb_last 73)(bol_pos_last 1627)(bp 1636)(ep 1637)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 73)(bol_pos 1627)(line_nb_last 73)(bol_pos_last 1627)(bp 1636)(ep 1637)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 73)(bol_pos 1627)(line_nb_last 73)(bol_pos_last 1627)(bp 1631)(ep 1637)))))((v(((((v(CPatCstr((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 74)(bol_pos 1638)(line_nb_last 74)(bol_pos_last 1638)(bp 1642)(ep 1643)))))(((v(CPatAtom(((v(Ser_Qualid(DirPath)(Id p)))(loc(((fname(InFile(dirpath)ufile))(line_nb 74)(bol_pos 1638)(line_nb_last 74)(bol_pos_last 1638)(bp 1644)(ep 1645))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 74)(bol_pos 1638)(line_nb_last 74)(bol_pos_last 1638)(bp 1644)(ep 1645))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 74)(bol_pos 1638)(line_nb_last 74)(bol_pos_last 1638)(bp 1642)(ep 1645)))))))((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 74)(bol_pos 1638)(line_nb_last 74)(bol_pos_last 1638)(bp 1649)(ep 1650)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 74)(bol_pos 1638)(line_nb_last 74)(bol_pos_last 1638)(bp 1649)(ep 1650)))))((((v(CNotation(InConstrEntry"_ + _")((((v(CRef((v(Ser_Qualid(DirPath)(Id p)))(loc(((fname(InFile(dirpath)ufile))(line_nb 74)(bol_pos 1638)(line_nb_last 74)(bol_pos_last 1638)(bp 1652)(ep 1653)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 74)(bol_pos 1638)(line_nb_last 74)(bol_pos_last 1638)(bp 1652)(ep 1653)))))((v(CRef((v(Ser_Qualid(DirPath)(Id m)))(loc(((fname(InFile(dirpath)ufile))(line_nb 74)(bol_pos 1638)(line_nb_last 74)(bol_pos_last 1638)(bp 1656)(ep 1657)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 74)(bol_pos 1638)(line_nb_last 74)(bol_pos_last 1638)(bp 1656)(ep 1657)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 74)(bol_pos 1638)(line_nb_last 74)(bol_pos_last 1638)(bp 1652)(ep 1657)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 74)(bol_pos 1638)(line_nb_last 74)(bol_pos_last 1638)(bp 1649)(ep 1658)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 74)(bol_pos 1638)(line_nb_last 74)(bol_pos_last 1638)(bp 1642)(ep 1658))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 72)(bol_pos 1612)(line_nb_last 75)(bol_pos_last 1659)(bp 1614)(ep 1664)))))))(notations(((ntn_decl_string((v"n + m")(loc(((fname(InFile(dirpath)ufile))(line_nb 76)(bol_pos 1665)(line_nb_last 76)(bol_pos_last 1665)(bp 1671)(ep 1678))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id add)))(loc(((fname(InFile(dirpath)ufile))(line_nb 76)(bol_pos 1665)(line_nb_last 76)(bol_pos_last 1665)(bp 1683)(ep 1686)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 76)(bol_pos 1665)(line_nb_last 76)(bol_pos_last 1665)(bp 1683)(ep 1686)))))((((v(CRef((v(Ser_Qualid(DirPath)(Id n)))(loc(((fname(InFile(dirpath)ufile))(line_nb 76)(bol_pos 1665)(line_nb_last 76)(bol_pos_last 1665)(bp 1687)(ep 1688)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 76)(bol_pos 1665)(line_nb_last 76)(bol_pos_last 1665)(bp 1687)(ep 1688))))))(((v(CRef((v(Ser_Qualid(DirPath)(Id m)))(loc(((fname(InFile(dirpath)ufile))(line_nb 76)(bol_pos 1665)(line_nb_last 76)(bol_pos_last 1665)(bp 1689)(ep 1690)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 76)(bol_pos 1665)(line_nb_last 76)(bol_pos_last 1665)(bp 1689)(ep 1690)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 76)(bol_pos 1665)(line_nb_last 76)(bol_pos_last 1665)(bp 1683)(ep 1690))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 71)(bol_pos 1592)(line_nb_last 76)(bol_pos_last 1665)(bp 1592)(ep 1704))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacFixpoint NoDischarge(((fname((v(Id sub))(loc(((fname(InFile(dirpath)ufile))(line_nb 78)(bol_pos 1706)(line_nb_last 78)(bol_pos_last 1706)(bp 1715)(ep 1718))))))(univs)(rec_order)(binders((CLocalAssum(((v(Name(Id n)))(loc(((fname(InFile(dirpath)ufile))(line_nb 78)(bol_pos 1706)(line_nb_last 78)(bol_pos_last 1706)(bp 1719)(ep 1720))))))(Default Explicit)((v(CHoleIntroAnonymous))(loc(((fname(InFile(dirpath)ufile))(line_nb 78)(bol_pos 1706)(line_nb_last 78)(bol_pos_last 1706)(bp 1719)(ep 1720))))))(CLocalAssum(((v(Name(Id m)))(loc(((fname(InFile(dirpath)ufile))(line_nb 78)(bol_pos 1706)(line_nb_last 78)(bol_pos_last 1706)(bp 1721)(ep 1722))))))(Default Explicit)((v(CHoleIntroAnonymous))(loc(((fname(InFile(dirpath)ufile))(line_nb 78)(bol_pos 1706)(line_nb_last 78)(bol_pos_last 1706)(bp 1721)(ep 1722))))))))(rtype((v(CHoleIntroAnonymous))(loc(((fname(InFile(dirpath)ufile))(line_nb 78)(bol_pos 1706)(line_nb_last 78)(bol_pos_last 1706)(bp 1722)(ep 1722))))))(body_def(((v(CCases RegularStyle((((v(CRef((v(Ser_Qualid(DirPath)(Id n)))(loc(((fname(InFile(dirpath)ufile))(line_nb 79)(bol_pos 1726)(line_nb_last 79)(bol_pos_last 1726)(bp 1734)(ep 1735)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 79)(bol_pos 1726)(line_nb_last 79)(bol_pos_last 1726)(bp 1734)(ep 1735))))))(((v(CRef((v(Ser_Qualid(DirPath)(Id m)))(loc(((fname(InFile(dirpath)ufile))(line_nb 79)(bol_pos 1726)(line_nb_last 79)(bol_pos_last 1726)(bp 1737)(ep 1738)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 79)(bol_pos 1726)(line_nb_last 79)(bol_pos_last 1726)(bp 1737)(ep 1738)))))))(((v(((((v(CPatCstr((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 80)(bol_pos 1744)(line_nb_last 80)(bol_pos_last 1744)(bp 1748)(ep 1749)))))(((v(CPatAtom(((v(Ser_Qualid(DirPath)(Id k)))(loc(((fname(InFile(dirpath)ufile))(line_nb 80)(bol_pos 1744)(line_nb_last 80)(bol_pos_last 1744)(bp 1750)(ep 1751))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 80)(bol_pos 1744)(line_nb_last 80)(bol_pos_last 1744)(bp 1750)(ep 1751))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 80)(bol_pos 1744)(line_nb_last 80)(bol_pos_last 1744)(bp 1748)(ep 1751)))))((v(CPatCstr((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 80)(bol_pos 1744)(line_nb_last 80)(bol_pos_last 1744)(bp 1753)(ep 1754)))))(((v(CPatAtom(((v(Ser_Qualid(DirPath)(Id l)))(loc(((fname(InFile(dirpath)ufile))(line_nb 80)(bol_pos 1744)(line_nb_last 80)(bol_pos_last 1744)(bp 1755)(ep 1756))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 80)(bol_pos 1744)(line_nb_last 80)(bol_pos_last 1744)(bp 1755)(ep 1756))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 80)(bol_pos 1744)(line_nb_last 80)(bol_pos_last 1744)(bp 1753)(ep 1756)))))))((v(CNotation(InConstrEntry"_ - _")((((v(CRef((v(Ser_Qualid(DirPath)(Id k)))(loc(((fname(InFile(dirpath)ufile))(line_nb 80)(bol_pos 1744)(line_nb_last 80)(bol_pos_last 1744)(bp 1760)(ep 1761)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 80)(bol_pos 1744)(line_nb_last 80)(bol_pos_last 1744)(bp 1760)(ep 1761)))))((v(CRef((v(Ser_Qualid(DirPath)(Id l)))(loc(((fname(InFile(dirpath)ufile))(line_nb 80)(bol_pos 1744)(line_nb_last 80)(bol_pos_last 1744)(bp 1764)(ep 1765)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 80)(bol_pos 1744)(line_nb_last 80)(bol_pos_last 1744)(bp 1764)(ep 1765)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 80)(bol_pos 1744)(line_nb_last 80)(bol_pos_last 1744)(bp 1760)(ep 1765)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 80)(bol_pos 1744)(line_nb_last 80)(bol_pos_last 1744)(bp 1748)(ep 1765)))))((v(((((v(CPatAtom))(loc(((fname(InFile(dirpath)ufile))(line_nb 81)(bol_pos 1766)(line_nb_last 81)(bol_pos_last 1766)(bp 1770)(ep 1771)))))((v(CPatAtom))(loc(((fname(InFile(dirpath)ufile))(line_nb 81)(bol_pos 1766)(line_nb_last 81)(bol_pos_last 1766)(bp 1773)(ep 1774)))))))((v(CRef((v(Ser_Qualid(DirPath)(Id n)))(loc(((fname(InFile(dirpath)ufile))(line_nb 81)(bol_pos 1766)(line_nb_last 81)(bol_pos_last 1766)(bp 1778)(ep 1779)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 81)(bol_pos 1766)(line_nb_last 81)(bol_pos_last 1766)(bp 1778)(ep 1779)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 81)(bol_pos 1766)(line_nb_last 81)(bol_pos_last 1766)(bp 1770)(ep 1779))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 79)(bol_pos 1726)(line_nb_last 82)(bol_pos_last 1780)(bp 1728)(ep 1785)))))))(notations(((ntn_decl_string((v"n - m")(loc(((fname(InFile(dirpath)ufile))(line_nb 83)(bol_pos 1786)(line_nb_last 83)(bol_pos_last 1786)(bp 1792)(ep 1799))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id sub)))(loc(((fname(InFile(dirpath)ufile))(line_nb 83)(bol_pos 1786)(line_nb_last 83)(bol_pos_last 1786)(bp 1804)(ep 1807)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 83)(bol_pos 1786)(line_nb_last 83)(bol_pos_last 1786)(bp 1804)(ep 1807)))))((((v(CRef((v(Ser_Qualid(DirPath)(Id n)))(loc(((fname(InFile(dirpath)ufile))(line_nb 83)(bol_pos 1786)(line_nb_last 83)(bol_pos_last 1786)(bp 1808)(ep 1809)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 83)(bol_pos 1786)(line_nb_last 83)(bol_pos_last 1786)(bp 1808)(ep 1809))))))(((v(CRef((v(Ser_Qualid(DirPath)(Id m)))(loc(((fname(InFile(dirpath)ufile))(line_nb 83)(bol_pos 1786)(line_nb_last 83)(bol_pos_last 1786)(bp 1810)(ep 1811)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 83)(bol_pos 1786)(line_nb_last 83)(bol_pos_last 1786)(bp 1810)(ep 1811)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 83)(bol_pos 1786)(line_nb_last 83)(bol_pos_last 1786)(bp 1804)(ep 1811))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 78)(bol_pos 1706)(line_nb_last 83)(bol_pos_last 1786)(bp 1706)(ep 1825))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacDefinition(NoDischarge Definition)(((v(Name(Id mul)))(loc(((fname(InFile(dirpath)ufile))(line_nb 86)(bol_pos 1882)(line_nb_last 86)(bol_pos_last 1882)(bp 1893)(ep 1896))))))(ProveBody((v(CNotation(InConstrEntry"_ -> _")((((v(CRef((v(Ser_Qualid(DirPath)(Id nat)))(loc(((fname(InFile(dirpath)ufile))(line_nb 86)(bol_pos 1882)(line_nb_last 86)(bol_pos_last 1882)(bp 1899)(ep 1902)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 86)(bol_pos 1882)(line_nb_last 86)(bol_pos_last 1882)(bp 1899)(ep 1902)))))((v(CNotation(InConstrEntry"_ -> _")((((v(CRef((v(Ser_Qualid(DirPath)(Id nat)))(loc(((fname(InFile(dirpath)ufile))(line_nb 86)(bol_pos 1882)(line_nb_last 86)(bol_pos_last 1882)(bp 1906)(ep 1909)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 86)(bol_pos 1882)(line_nb_last 86)(bol_pos_last 1882)(bp 1906)(ep 1909)))))((v(CRef((v(Ser_Qualid(DirPath)(Id nat)))(loc(((fname(InFile(dirpath)ufile))(line_nb 86)(bol_pos 1882)(line_nb_last 86)(bol_pos_last 1882)(bp 1913)(ep 1916)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 86)(bol_pos 1882)(line_nb_last 86)(bol_pos_last 1882)(bp 1913)(ep 1916)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 86)(bol_pos 1882)(line_nb_last 86)(bol_pos_last 1882)(bp 1906)(ep 1916)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 86)(bol_pos 1882)(line_nb_last 86)(bol_pos_last 1882)(bp 1899)(ep 1916)))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 86)(bol_pos 1882)(line_nb_last 86)(bol_pos_last 1882)(bp 1882)(ep 1917))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacProof)))))(loc(((fname(InFile(dirpath)ufile))(line_nb 87)(bol_pos 1918)(line_nb_last 87)(bol_pos_last 1918)(bp 1918)(ep 1924))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacExtend(VernacSolve 0)((GenArg(Rawwit(OptArg(ExtraArg ltac_selector))))(GenArg(Rawwit(OptArg(ExtraArg ltac_info))))(GenArg(Rawwit(ExtraArg tactic))((v(TacAtom(TacIntroPattern false(((v(IntroNaming(IntroIdentifier(Id n))))(loc(((fname(InFile(dirpath)ufile))(line_nb 88)(bol_pos 1925)(line_nb_last 88)(bol_pos_last 1925)(bp 1934)(ep 1935)))))((v(IntroNaming(IntroIdentifier(Id m))))(loc(((fname(InFile(dirpath)ufile))(line_nb 88)(bol_pos 1925)(line_nb_last 88)(bol_pos_last 1925)(bp 1936)(ep 1937)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 88)(bol_pos 1925)(line_nb_last 88)(bol_pos_last 1925)(bp 1927)(ep 1937))))))(GenArg(Rawwit(ExtraArg ltac_use_default))false)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 88)(bol_pos 1925)(line_nb_last 88)(bol_pos_last 1925)(bp 1927)(ep 1938))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacExtend(VernacSolve 0)((GenArg(Rawwit(OptArg(ExtraArg ltac_selector))))(GenArg(Rawwit(OptArg(ExtraArg ltac_info))))(GenArg(Rawwit(ExtraArg tactic))((v(TacAtom(TacInductionDestruct true false(((((ElimOnIdent((v(Id n))(loc(((fname(InFile(dirpath)ufile))(line_nb 89)(bol_pos 1939)(line_nb_last 89)(bol_pos_last 1939)(bp 1951)(ep 1952)))))))(((ArgArg((v(IntroOrPattern((((v(IntroNaming(IntroIdentifier(Id p))))(loc(((fname(InFile(dirpath)ufile))(line_nb 89)(bol_pos 1939)(line_nb_last 89)(bol_pos_last 1939)(bp 1958)(ep 1959)))))((v(IntroNaming(IntroIdentifier(Id pm))))(loc(((fname(InFile(dirpath)ufile))(line_nb 89)(bol_pos 1939)(line_nb_last 89)(bol_pos_last 1939)(bp 1960)(ep 1962)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 89)(bol_pos 1939)(line_nb_last 89)(bol_pos_last 1939)(bp 1956)(ep 1963))))))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 89)(bol_pos 1939)(line_nb_last 89)(bol_pos_last 1939)(bp 1941)(ep 1963))))))(GenArg(Rawwit(ExtraArg ltac_use_default))false)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 89)(bol_pos 1939)(line_nb_last 89)(bol_pos_last 1939)(bp 1941)(ep 1964))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacBullet(Dash 1))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 90)(bol_pos 1965)(line_nb_last 90)(bol_pos_last 1965)(bp 1967)(ep 1968))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacExtend(VernacSolve 0)((GenArg(Rawwit(OptArg(ExtraArg ltac_selector))))(GenArg(Rawwit(OptArg(ExtraArg ltac_info))))(GenArg(Rawwit(ExtraArg tactic))((v(TacAlias((KerName(MPfile(DirPath((Id Ltac)(Id Init)(Id Coq))))(Id exact_#_52192787))((TacGeneric(GenArg(Rawwit(ExtraArg uconstr))((v(CRef((v(Ser_Qualid(DirPath)(Id O)))(loc(((fname(InFile(dirpath)ufile))(line_nb 90)(bol_pos 1965)(line_nb_last 90)(bol_pos_last 1965)(bp 1975)(ep 1976)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 90)(bol_pos 1965)(line_nb_last 90)(bol_pos_last 1965)(bp 1975)(ep 1976)))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 90)(bol_pos 1965)(line_nb_last 90)(bol_pos_last 1965)(bp 1969)(ep 1976))))))(GenArg(Rawwit(ExtraArg ltac_use_default))false)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 90)(bol_pos 1965)(line_nb_last 90)(bol_pos_last 1965)(bp 1969)(ep 1977))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacBullet(Dash 1))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 91)(bol_pos 1978)(line_nb_last 91)(bol_pos_last 1978)(bp 1980)(ep 1981))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacExtend(VernacSolve 0)((GenArg(Rawwit(OptArg(ExtraArg ltac_selector))))(GenArg(Rawwit(OptArg(ExtraArg ltac_info))))(GenArg(Rawwit(ExtraArg tactic))((v(TacAlias((KerName(MPfile(DirPath((Id Ltac)(Id Init)(Id Coq))))(Id exact_#_52192787))((TacGeneric(GenArg(Rawwit(ExtraArg uconstr))((v(CNotation(InConstrEntry"_ + _")((((v(CRef((v(Ser_Qualid(DirPath)(Id pm)))(loc(((fname(InFile(dirpath)ufile))(line_nb 91)(bol_pos 1978)(line_nb_last 91)(bol_pos_last 1978)(bp 1989)(ep 1991)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 91)(bol_pos 1978)(line_nb_last 91)(bol_pos_last 1978)(bp 1989)(ep 1991)))))((v(CRef((v(Ser_Qualid(DirPath)(Id m)))(loc(((fname(InFile(dirpath)ufile))(line_nb 91)(bol_pos 1978)(line_nb_last 91)(bol_pos_last 1978)(bp 1994)(ep 1995)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 91)(bol_pos 1978)(line_nb_last 91)(bol_pos_last 1978)(bp 1994)(ep 1995)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 91)(bol_pos 1978)(line_nb_last 91)(bol_pos_last 1978)(bp 1989)(ep 1995)))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 91)(bol_pos 1978)(line_nb_last 91)(bol_pos_last 1978)(bp 1982)(ep 1996))))))(GenArg(Rawwit(ExtraArg ltac_use_default))false)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 91)(bol_pos 1978)(line_nb_last 91)(bol_pos_last 1978)(bp 1982)(ep 1997))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacEndProof(Proved Transparent))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 92)(bol_pos 1998)(line_nb_last 92)(bol_pos_last 1998)(bp 1998)(ep 2006))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v"n * m")(loc(((fname(InFile(dirpath)ufile))(line_nb 94)(bol_pos 2008)(line_nb_last 94)(bol_pos_last 2008)(bp 2017)(ep 2024))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id mul)))(loc(((fname(InFile(dirpath)ufile))(line_nb 94)(bol_pos 2008)(line_nb_last 94)(bol_pos_last 2008)(bp 2029)(ep 2032)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 94)(bol_pos 2008)(line_nb_last 94)(bol_pos_last 2008)(bp 2029)(ep 2032)))))((((v(CRef((v(Ser_Qualid(DirPath)(Id n)))(loc(((fname(InFile(dirpath)ufile))(line_nb 94)(bol_pos 2008)(line_nb_last 94)(bol_pos_last 2008)(bp 2033)(ep 2034)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 94)(bol_pos 2008)(line_nb_last 94)(bol_pos_last 2008)(bp 2033)(ep 2034))))))(((v(CRef((v(Ser_Qualid(DirPath)(Id m)))(loc(((fname(InFile(dirpath)ufile))(line_nb 94)(bol_pos 2008)(line_nb_last 94)(bol_pos_last 2008)(bp 2035)(ep 2036)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 94)(bol_pos 2008)(line_nb_last 94)(bol_pos_last 2008)(bp 2035)(ep 2036)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 94)(bol_pos 2008)(line_nb_last 94)(bol_pos_last 2008)(bp 2029)(ep 2036))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 94)(bol_pos 2008)(line_nb_last 94)(bol_pos_last 2008)(bp 2008)(ep 2050))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacFixpoint NoDischarge(((fname((v(Id max))(loc(((fname(InFile(dirpath)ufile))(line_nb 96)(bol_pos 2052)(line_nb_last 96)(bol_pos_last 2052)(bp 2061)(ep 2064))))))(univs)(rec_order)(binders((CLocalAssum(((v(Name(Id n)))(loc(((fname(InFile(dirpath)ufile))(line_nb 96)(bol_pos 2052)(line_nb_last 96)(bol_pos_last 2052)(bp 2065)(ep 2066))))))(Default Explicit)((v(CHoleIntroAnonymous))(loc(((fname(InFile(dirpath)ufile))(line_nb 96)(bol_pos 2052)(line_nb_last 96)(bol_pos_last 2052)(bp 2065)(ep 2066))))))(CLocalAssum(((v(Name(Id m)))(loc(((fname(InFile(dirpath)ufile))(line_nb 96)(bol_pos 2052)(line_nb_last 96)(bol_pos_last 2052)(bp 2067)(ep 2068))))))(Default Explicit)((v(CHoleIntroAnonymous))(loc(((fname(InFile(dirpath)ufile))(line_nb 96)(bol_pos 2052)(line_nb_last 96)(bol_pos_last 2052)(bp 2067)(ep 2068))))))))(rtype((v(CHoleIntroAnonymous))(loc(((fname(InFile(dirpath)ufile))(line_nb 96)(bol_pos 2052)(line_nb_last 96)(bol_pos_last 2052)(bp 2068)(ep 2068))))))(body_def(((v(CCases RegularStyle((((v(CRef((v(Ser_Qualid(DirPath)(Id n)))(loc(((fname(InFile(dirpath)ufile))(line_nb 97)(bol_pos 2072)(line_nb_last 97)(bol_pos_last 2072)(bp 2080)(ep 2081)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 97)(bol_pos 2072)(line_nb_last 97)(bol_pos_last 2072)(bp 2080)(ep 2081))))))(((v(CRef((v(Ser_Qualid(DirPath)(Id m)))(loc(((fname(InFile(dirpath)ufile))(line_nb 97)(bol_pos 2072)(line_nb_last 97)(bol_pos_last 2072)(bp 2083)(ep 2084)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 97)(bol_pos 2072)(line_nb_last 97)(bol_pos_last 2072)(bp 2083)(ep 2084)))))))(((v(((((v(CPatAtom(((v(Ser_Qualid(DirPath)(Id O)))(loc(((fname(InFile(dirpath)ufile))(line_nb 98)(bol_pos 2090)(line_nb_last 98)(bol_pos_last 2090)(bp 2096)(ep 2097))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 98)(bol_pos 2090)(line_nb_last 98)(bol_pos_last 2090)(bp 2096)(ep 2097)))))((v(CPatAtom))(loc(((fname(InFile(dirpath)ufile))(line_nb 98)(bol_pos 2090)(line_nb_last 98)(bol_pos_last 2090)(bp 2099)(ep 2100)))))))((v(CRef((v(Ser_Qualid(DirPath)(Id m)))(loc(((fname(InFile(dirpath)ufile))(line_nb 98)(bol_pos 2090)(line_nb_last 98)(bol_pos_last 2090)(bp 2104)(ep 2105)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 98)(bol_pos 2090)(line_nb_last 98)(bol_pos_last 2090)(bp 2104)(ep 2105)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 98)(bol_pos 2090)(line_nb_last 98)(bol_pos_last 2090)(bp 2096)(ep 2105)))))((v(((((v(CPatCstr((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 99)(bol_pos 2106)(line_nb_last 99)(bol_pos_last 2106)(bp 2112)(ep 2113)))))(((v(CPatAtom(((v(Ser_Qualid(DirPath)(Id"n'")))(loc(((fname(InFile(dirpath)ufile))(line_nb 99)(bol_pos 2106)(line_nb_last 99)(bol_pos_last 2106)(bp 2114)(ep 2116))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 99)(bol_pos 2106)(line_nb_last 99)(bol_pos_last 2106)(bp 2114)(ep 2116))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 99)(bol_pos 2106)(line_nb_last 99)(bol_pos_last 2106)(bp 2112)(ep 2116)))))((v(CPatAtom(((v(Ser_Qualid(DirPath)(Id O)))(loc(((fname(InFile(dirpath)ufile))(line_nb 99)(bol_pos 2106)(line_nb_last 99)(bol_pos_last 2106)(bp 2118)(ep 2119))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 99)(bol_pos 2106)(line_nb_last 99)(bol_pos_last 2106)(bp 2118)(ep 2119)))))))((v(CRef((v(Ser_Qualid(DirPath)(Id n)))(loc(((fname(InFile(dirpath)ufile))(line_nb 99)(bol_pos 2106)(line_nb_last 99)(bol_pos_last 2106)(bp 2123)(ep 2124)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 99)(bol_pos 2106)(line_nb_last 99)(bol_pos_last 2106)(bp 2123)(ep 2124)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 99)(bol_pos 2106)(line_nb_last 99)(bol_pos_last 2106)(bp 2112)(ep 2124)))))((v(((((v(CPatCstr((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2131)(ep 2132)))))(((v(CPatAtom(((v(Ser_Qualid(DirPath)(Id"n'")))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2133)(ep 2135))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2133)(ep 2135))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2131)(ep 2135)))))((v(CPatCstr((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2137)(ep 2138)))))(((v(CPatAtom(((v(Ser_Qualid(DirPath)(Id"m'")))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2139)(ep 2141))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2139)(ep 2141))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2137)(ep 2141)))))))((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2145)(ep 2146)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2145)(ep 2146)))))((((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id max)))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2148)(ep 2151)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2148)(ep 2151)))))((((v(CRef((v(Ser_Qualid(DirPath)(Id"n'")))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2152)(ep 2154)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2152)(ep 2154))))))(((v(CRef((v(Ser_Qualid(DirPath)(Id"m'")))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2155)(ep 2157)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2155)(ep 2157)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2148)(ep 2157)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2145)(ep 2158)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 100)(bol_pos 2125)(line_nb_last 100)(bol_pos_last 2125)(bp 2131)(ep 2158))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 97)(bol_pos 2072)(line_nb_last 101)(bol_pos_last 2159)(bp 2074)(ep 2164)))))))(notations))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 96)(bol_pos 2052)(line_nb_last 101)(bol_pos_last 2159)(bp 2052)(ep 2165))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacFixpoint NoDischarge(((fname((v(Id min))(loc(((fname(InFile(dirpath)ufile))(line_nb 103)(bol_pos 2167)(line_nb_last 103)(bol_pos_last 2167)(bp 2176)(ep 2179))))))(univs)(rec_order)(binders((CLocalAssum(((v(Name(Id n)))(loc(((fname(InFile(dirpath)ufile))(line_nb 103)(bol_pos 2167)(line_nb_last 103)(bol_pos_last 2167)(bp 2180)(ep 2181))))))(Default Explicit)((v(CHoleIntroAnonymous))(loc(((fname(InFile(dirpath)ufile))(line_nb 103)(bol_pos 2167)(line_nb_last 103)(bol_pos_last 2167)(bp 2180)(ep 2181))))))(CLocalAssum(((v(Name(Id m)))(loc(((fname(InFile(dirpath)ufile))(line_nb 103)(bol_pos 2167)(line_nb_last 103)(bol_pos_last 2167)(bp 2182)(ep 2183))))))(Default Explicit)((v(CHoleIntroAnonymous))(loc(((fname(InFile(dirpath)ufile))(line_nb 103)(bol_pos 2167)(line_nb_last 103)(bol_pos_last 2167)(bp 2182)(ep 2183))))))))(rtype((v(CHoleIntroAnonymous))(loc(((fname(InFile(dirpath)ufile))(line_nb 103)(bol_pos 2167)(line_nb_last 103)(bol_pos_last 2167)(bp 2183)(ep 2183))))))(body_def(((v(CCases RegularStyle((((v(CRef((v(Ser_Qualid(DirPath)(Id n)))(loc(((fname(InFile(dirpath)ufile))(line_nb 104)(bol_pos 2187)(line_nb_last 104)(bol_pos_last 2187)(bp 2195)(ep 2196)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 104)(bol_pos 2187)(line_nb_last 104)(bol_pos_last 2187)(bp 2195)(ep 2196))))))(((v(CRef((v(Ser_Qualid(DirPath)(Id m)))(loc(((fname(InFile(dirpath)ufile))(line_nb 104)(bol_pos 2187)(line_nb_last 104)(bol_pos_last 2187)(bp 2198)(ep 2199)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 104)(bol_pos 2187)(line_nb_last 104)(bol_pos_last 2187)(bp 2198)(ep 2199)))))))(((v(((((v(CPatAtom(((v(Ser_Qualid(DirPath)(Id O)))(loc(((fname(InFile(dirpath)ufile))(line_nb 105)(bol_pos 2205)(line_nb_last 105)(bol_pos_last 2205)(bp 2211)(ep 2212))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 105)(bol_pos 2205)(line_nb_last 105)(bol_pos_last 2205)(bp 2211)(ep 2212)))))((v(CPatAtom))(loc(((fname(InFile(dirpath)ufile))(line_nb 105)(bol_pos 2205)(line_nb_last 105)(bol_pos_last 2205)(bp 2214)(ep 2215)))))))((v(CRef((v(Ser_Qualid(DirPath)(Id O)))(loc(((fname(InFile(dirpath)ufile))(line_nb 105)(bol_pos 2205)(line_nb_last 105)(bol_pos_last 2205)(bp 2219)(ep 2220)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 105)(bol_pos 2205)(line_nb_last 105)(bol_pos_last 2205)(bp 2219)(ep 2220)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 105)(bol_pos 2205)(line_nb_last 105)(bol_pos_last 2205)(bp 2211)(ep 2220)))))((v(((((v(CPatCstr((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 106)(bol_pos 2221)(line_nb_last 106)(bol_pos_last 2221)(bp 2227)(ep 2228)))))(((v(CPatAtom(((v(Ser_Qualid(DirPath)(Id"n'")))(loc(((fname(InFile(dirpath)ufile))(line_nb 106)(bol_pos 2221)(line_nb_last 106)(bol_pos_last 2221)(bp 2229)(ep 2231))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 106)(bol_pos 2221)(line_nb_last 106)(bol_pos_last 2221)(bp 2229)(ep 2231))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 106)(bol_pos 2221)(line_nb_last 106)(bol_pos_last 2221)(bp 2227)(ep 2231)))))((v(CPatAtom(((v(Ser_Qualid(DirPath)(Id O)))(loc(((fname(InFile(dirpath)ufile))(line_nb 106)(bol_pos 2221)(line_nb_last 106)(bol_pos_last 2221)(bp 2233)(ep 2234))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 106)(bol_pos 2221)(line_nb_last 106)(bol_pos_last 2221)(bp 2233)(ep 2234)))))))((v(CRef((v(Ser_Qualid(DirPath)(Id O)))(loc(((fname(InFile(dirpath)ufile))(line_nb 106)(bol_pos 2221)(line_nb_last 106)(bol_pos_last 2221)(bp 2238)(ep 2239)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 106)(bol_pos 2221)(line_nb_last 106)(bol_pos_last 2221)(bp 2238)(ep 2239)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 106)(bol_pos 2221)(line_nb_last 106)(bol_pos_last 2221)(bp 2227)(ep 2239)))))((v(((((v(CPatCstr((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2246)(ep 2247)))))(((v(CPatAtom(((v(Ser_Qualid(DirPath)(Id"n'")))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2248)(ep 2250))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2248)(ep 2250))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2246)(ep 2250)))))((v(CPatCstr((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2252)(ep 2253)))))(((v(CPatAtom(((v(Ser_Qualid(DirPath)(Id"m'")))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2254)(ep 2256))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2254)(ep 2256))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2252)(ep 2256)))))))((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2260)(ep 2261)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2260)(ep 2261)))))((((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id min)))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2263)(ep 2266)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2263)(ep 2266)))))((((v(CRef((v(Ser_Qualid(DirPath)(Id"n'")))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2267)(ep 2269)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2267)(ep 2269))))))(((v(CRef((v(Ser_Qualid(DirPath)(Id"m'")))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2270)(ep 2272)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2270)(ep 2272)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2263)(ep 2272)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2260)(ep 2273)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 107)(bol_pos 2240)(line_nb_last 107)(bol_pos_last 2240)(bp 2246)(ep 2273))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 104)(bol_pos 2187)(line_nb_last 108)(bol_pos_last 2274)(bp 2189)(ep 2279)))))))(notations))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 103)(bol_pos 2167)(line_nb_last 108)(bol_pos_last 2274)(bp 2167)(ep 2280))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 0)(loc(((fname(InFile(dirpath)ufile))(line_nb 110)(bol_pos 2282)(line_nb_last 110)(bol_pos_last 2282)(bp 2292)(ep 2295))))))(ntn_decl_interp((v(CRef((v(Ser_Qualid(DirPath)(Id O)))(loc(((fname(InFile(dirpath)ufile))(line_nb 110)(bol_pos 2282)(line_nb_last 110)(bol_pos_last 2282)(bp 2300)(ep 2301)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 110)(bol_pos 2282)(line_nb_last 110)(bol_pos_last 2282)(bp 2300)(ep 2301))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 110)(bol_pos 2282)(line_nb_last 110)(bol_pos_last 2282)(bp 2282)(ep 2315))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 1)(loc(((fname(InFile(dirpath)ufile))(line_nb 111)(bol_pos 2316)(line_nb_last 111)(bol_pos_last 2316)(bp 2326)(ep 2329))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 111)(bol_pos 2316)(line_nb_last 111)(bol_pos_last 2316)(bp 2334)(ep 2335)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 111)(bol_pos 2316)(line_nb_last 111)(bol_pos_last 2316)(bp 2334)(ep 2335)))))((((v(CPrim(Number(SPlus((int 0)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 111)(bol_pos 2316)(line_nb_last 111)(bol_pos_last 2316)(bp 2336)(ep 2337)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 111)(bol_pos 2316)(line_nb_last 111)(bol_pos_last 2316)(bp 2334)(ep 2337))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 111)(bol_pos 2316)(line_nb_last 111)(bol_pos_last 2316)(bp 2316)(ep 2351))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 2)(loc(((fname(InFile(dirpath)ufile))(line_nb 112)(bol_pos 2352)(line_nb_last 112)(bol_pos_last 2352)(bp 2362)(ep 2365))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 112)(bol_pos 2352)(line_nb_last 112)(bol_pos_last 2352)(bp 2370)(ep 2371)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 112)(bol_pos 2352)(line_nb_last 112)(bol_pos_last 2352)(bp 2370)(ep 2371)))))((((v(CPrim(Number(SPlus((int 1)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 112)(bol_pos 2352)(line_nb_last 112)(bol_pos_last 2352)(bp 2372)(ep 2373)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 112)(bol_pos 2352)(line_nb_last 112)(bol_pos_last 2352)(bp 2370)(ep 2373))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 112)(bol_pos 2352)(line_nb_last 112)(bol_pos_last 2352)(bp 2352)(ep 2387))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 3)(loc(((fname(InFile(dirpath)ufile))(line_nb 113)(bol_pos 2388)(line_nb_last 113)(bol_pos_last 2388)(bp 2398)(ep 2401))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 113)(bol_pos 2388)(line_nb_last 113)(bol_pos_last 2388)(bp 2406)(ep 2407)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 113)(bol_pos 2388)(line_nb_last 113)(bol_pos_last 2388)(bp 2406)(ep 2407)))))((((v(CPrim(Number(SPlus((int 2)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 113)(bol_pos 2388)(line_nb_last 113)(bol_pos_last 2388)(bp 2408)(ep 2409)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 113)(bol_pos 2388)(line_nb_last 113)(bol_pos_last 2388)(bp 2406)(ep 2409))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 113)(bol_pos 2388)(line_nb_last 113)(bol_pos_last 2388)(bp 2388)(ep 2423))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 4)(loc(((fname(InFile(dirpath)ufile))(line_nb 114)(bol_pos 2424)(line_nb_last 114)(bol_pos_last 2424)(bp 2434)(ep 2437))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 114)(bol_pos 2424)(line_nb_last 114)(bol_pos_last 2424)(bp 2442)(ep 2443)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 114)(bol_pos 2424)(line_nb_last 114)(bol_pos_last 2424)(bp 2442)(ep 2443)))))((((v(CPrim(Number(SPlus((int 3)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 114)(bol_pos 2424)(line_nb_last 114)(bol_pos_last 2424)(bp 2444)(ep 2445)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 114)(bol_pos 2424)(line_nb_last 114)(bol_pos_last 2424)(bp 2442)(ep 2445))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 114)(bol_pos 2424)(line_nb_last 114)(bol_pos_last 2424)(bp 2424)(ep 2459))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 5)(loc(((fname(InFile(dirpath)ufile))(line_nb 115)(bol_pos 2460)(line_nb_last 115)(bol_pos_last 2460)(bp 2470)(ep 2473))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 115)(bol_pos 2460)(line_nb_last 115)(bol_pos_last 2460)(bp 2478)(ep 2479)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 115)(bol_pos 2460)(line_nb_last 115)(bol_pos_last 2460)(bp 2478)(ep 2479)))))((((v(CPrim(Number(SPlus((int 4)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 115)(bol_pos 2460)(line_nb_last 115)(bol_pos_last 2460)(bp 2480)(ep 2481)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 115)(bol_pos 2460)(line_nb_last 115)(bol_pos_last 2460)(bp 2478)(ep 2481))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 115)(bol_pos 2460)(line_nb_last 115)(bol_pos_last 2460)(bp 2460)(ep 2495))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 6)(loc(((fname(InFile(dirpath)ufile))(line_nb 116)(bol_pos 2496)(line_nb_last 116)(bol_pos_last 2496)(bp 2506)(ep 2509))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 116)(bol_pos 2496)(line_nb_last 116)(bol_pos_last 2496)(bp 2514)(ep 2515)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 116)(bol_pos 2496)(line_nb_last 116)(bol_pos_last 2496)(bp 2514)(ep 2515)))))((((v(CPrim(Number(SPlus((int 5)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 116)(bol_pos 2496)(line_nb_last 116)(bol_pos_last 2496)(bp 2516)(ep 2517)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 116)(bol_pos 2496)(line_nb_last 116)(bol_pos_last 2496)(bp 2514)(ep 2517))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 116)(bol_pos 2496)(line_nb_last 116)(bol_pos_last 2496)(bp 2496)(ep 2531))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 7)(loc(((fname(InFile(dirpath)ufile))(line_nb 117)(bol_pos 2532)(line_nb_last 117)(bol_pos_last 2532)(bp 2542)(ep 2545))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 117)(bol_pos 2532)(line_nb_last 117)(bol_pos_last 2532)(bp 2550)(ep 2551)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 117)(bol_pos 2532)(line_nb_last 117)(bol_pos_last 2532)(bp 2550)(ep 2551)))))((((v(CPrim(Number(SPlus((int 6)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 117)(bol_pos 2532)(line_nb_last 117)(bol_pos_last 2532)(bp 2552)(ep 2553)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 117)(bol_pos 2532)(line_nb_last 117)(bol_pos_last 2532)(bp 2550)(ep 2553))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 117)(bol_pos 2532)(line_nb_last 117)(bol_pos_last 2532)(bp 2532)(ep 2567))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 8)(loc(((fname(InFile(dirpath)ufile))(line_nb 118)(bol_pos 2568)(line_nb_last 118)(bol_pos_last 2568)(bp 2578)(ep 2581))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 118)(bol_pos 2568)(line_nb_last 118)(bol_pos_last 2568)(bp 2586)(ep 2587)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 118)(bol_pos 2568)(line_nb_last 118)(bol_pos_last 2568)(bp 2586)(ep 2587)))))((((v(CPrim(Number(SPlus((int 7)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 118)(bol_pos 2568)(line_nb_last 118)(bol_pos_last 2568)(bp 2588)(ep 2589)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 118)(bol_pos 2568)(line_nb_last 118)(bol_pos_last 2568)(bp 2586)(ep 2589))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 118)(bol_pos 2568)(line_nb_last 118)(bol_pos_last 2568)(bp 2568)(ep 2603))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 9)(loc(((fname(InFile(dirpath)ufile))(line_nb 119)(bol_pos 2604)(line_nb_last 119)(bol_pos_last 2604)(bp 2614)(ep 2617))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 119)(bol_pos 2604)(line_nb_last 119)(bol_pos_last 2604)(bp 2622)(ep 2623)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 119)(bol_pos 2604)(line_nb_last 119)(bol_pos_last 2604)(bp 2622)(ep 2623)))))((((v(CPrim(Number(SPlus((int 8)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 119)(bol_pos 2604)(line_nb_last 119)(bol_pos_last 2604)(bp 2624)(ep 2625)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 119)(bol_pos 2604)(line_nb_last 119)(bol_pos_last 2604)(bp 2622)(ep 2625))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 119)(bol_pos 2604)(line_nb_last 119)(bol_pos_last 2604)(bp 2604)(ep 2639))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 10)(loc(((fname(InFile(dirpath)ufile))(line_nb 120)(bol_pos 2640)(line_nb_last 120)(bol_pos_last 2640)(bp 2649)(ep 2653))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 120)(bol_pos 2640)(line_nb_last 120)(bol_pos_last 2640)(bp 2658)(ep 2659)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 120)(bol_pos 2640)(line_nb_last 120)(bol_pos_last 2640)(bp 2658)(ep 2659)))))((((v(CPrim(Number(SPlus((int 9)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 120)(bol_pos 2640)(line_nb_last 120)(bol_pos_last 2640)(bp 2660)(ep 2661)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 120)(bol_pos 2640)(line_nb_last 120)(bol_pos_last 2640)(bp 2658)(ep 2661))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 120)(bol_pos 2640)(line_nb_last 120)(bol_pos_last 2640)(bp 2640)(ep 2675))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 11)(loc(((fname(InFile(dirpath)ufile))(line_nb 121)(bol_pos 2676)(line_nb_last 121)(bol_pos_last 2676)(bp 2685)(ep 2689))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 121)(bol_pos 2676)(line_nb_last 121)(bol_pos_last 2676)(bp 2694)(ep 2695)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 121)(bol_pos 2676)(line_nb_last 121)(bol_pos_last 2676)(bp 2694)(ep 2695)))))((((v(CPrim(Number(SPlus((int 10)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 121)(bol_pos 2676)(line_nb_last 121)(bol_pos_last 2676)(bp 2696)(ep 2698)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 121)(bol_pos 2676)(line_nb_last 121)(bol_pos_last 2676)(bp 2694)(ep 2698))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 121)(bol_pos 2676)(line_nb_last 121)(bol_pos_last 2676)(bp 2676)(ep 2712))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 12)(loc(((fname(InFile(dirpath)ufile))(line_nb 122)(bol_pos 2713)(line_nb_last 122)(bol_pos_last 2713)(bp 2722)(ep 2726))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 122)(bol_pos 2713)(line_nb_last 122)(bol_pos_last 2713)(bp 2731)(ep 2732)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 122)(bol_pos 2713)(line_nb_last 122)(bol_pos_last 2713)(bp 2731)(ep 2732)))))((((v(CPrim(Number(SPlus((int 11)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 122)(bol_pos 2713)(line_nb_last 122)(bol_pos_last 2713)(bp 2733)(ep 2735)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 122)(bol_pos 2713)(line_nb_last 122)(bol_pos_last 2713)(bp 2731)(ep 2735))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 122)(bol_pos 2713)(line_nb_last 122)(bol_pos_last 2713)(bp 2713)(ep 2749))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 13)(loc(((fname(InFile(dirpath)ufile))(line_nb 123)(bol_pos 2750)(line_nb_last 123)(bol_pos_last 2750)(bp 2759)(ep 2763))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 123)(bol_pos 2750)(line_nb_last 123)(bol_pos_last 2750)(bp 2768)(ep 2769)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 123)(bol_pos 2750)(line_nb_last 123)(bol_pos_last 2750)(bp 2768)(ep 2769)))))((((v(CPrim(Number(SPlus((int 12)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 123)(bol_pos 2750)(line_nb_last 123)(bol_pos_last 2750)(bp 2770)(ep 2772)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 123)(bol_pos 2750)(line_nb_last 123)(bol_pos_last 2750)(bp 2768)(ep 2772))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 123)(bol_pos 2750)(line_nb_last 123)(bol_pos_last 2750)(bp 2750)(ep 2786))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 14)(loc(((fname(InFile(dirpath)ufile))(line_nb 124)(bol_pos 2787)(line_nb_last 124)(bol_pos_last 2787)(bp 2796)(ep 2800))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 124)(bol_pos 2787)(line_nb_last 124)(bol_pos_last 2787)(bp 2805)(ep 2806)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 124)(bol_pos 2787)(line_nb_last 124)(bol_pos_last 2787)(bp 2805)(ep 2806)))))((((v(CPrim(Number(SPlus((int 13)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 124)(bol_pos 2787)(line_nb_last 124)(bol_pos_last 2787)(bp 2807)(ep 2809)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 124)(bol_pos 2787)(line_nb_last 124)(bol_pos_last 2787)(bp 2805)(ep 2809))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 124)(bol_pos 2787)(line_nb_last 124)(bol_pos_last 2787)(bp 2787)(ep 2823))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 15)(loc(((fname(InFile(dirpath)ufile))(line_nb 125)(bol_pos 2824)(line_nb_last 125)(bol_pos_last 2824)(bp 2833)(ep 2837))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 125)(bol_pos 2824)(line_nb_last 125)(bol_pos_last 2824)(bp 2842)(ep 2843)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 125)(bol_pos 2824)(line_nb_last 125)(bol_pos_last 2824)(bp 2842)(ep 2843)))))((((v(CPrim(Number(SPlus((int 14)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 125)(bol_pos 2824)(line_nb_last 125)(bol_pos_last 2824)(bp 2844)(ep 2846)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 125)(bol_pos 2824)(line_nb_last 125)(bol_pos_last 2824)(bp 2842)(ep 2846))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 125)(bol_pos 2824)(line_nb_last 125)(bol_pos_last 2824)(bp 2824)(ep 2860))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 16)(loc(((fname(InFile(dirpath)ufile))(line_nb 126)(bol_pos 2861)(line_nb_last 126)(bol_pos_last 2861)(bp 2870)(ep 2874))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 126)(bol_pos 2861)(line_nb_last 126)(bol_pos_last 2861)(bp 2879)(ep 2880)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 126)(bol_pos 2861)(line_nb_last 126)(bol_pos_last 2861)(bp 2879)(ep 2880)))))((((v(CPrim(Number(SPlus((int 15)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 126)(bol_pos 2861)(line_nb_last 126)(bol_pos_last 2861)(bp 2881)(ep 2883)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 126)(bol_pos 2861)(line_nb_last 126)(bol_pos_last 2861)(bp 2879)(ep 2883))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 126)(bol_pos 2861)(line_nb_last 126)(bol_pos_last 2861)(bp 2861)(ep 2897))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 17)(loc(((fname(InFile(dirpath)ufile))(line_nb 127)(bol_pos 2898)(line_nb_last 127)(bol_pos_last 2898)(bp 2907)(ep 2911))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 127)(bol_pos 2898)(line_nb_last 127)(bol_pos_last 2898)(bp 2916)(ep 2917)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 127)(bol_pos 2898)(line_nb_last 127)(bol_pos_last 2898)(bp 2916)(ep 2917)))))((((v(CPrim(Number(SPlus((int 16)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 127)(bol_pos 2898)(line_nb_last 127)(bol_pos_last 2898)(bp 2918)(ep 2920)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 127)(bol_pos 2898)(line_nb_last 127)(bol_pos_last 2898)(bp 2916)(ep 2920))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 127)(bol_pos 2898)(line_nb_last 127)(bol_pos_last 2898)(bp 2898)(ep 2934))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 18)(loc(((fname(InFile(dirpath)ufile))(line_nb 128)(bol_pos 2935)(line_nb_last 128)(bol_pos_last 2935)(bp 2944)(ep 2948))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 128)(bol_pos 2935)(line_nb_last 128)(bol_pos_last 2935)(bp 2953)(ep 2954)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 128)(bol_pos 2935)(line_nb_last 128)(bol_pos_last 2935)(bp 2953)(ep 2954)))))((((v(CPrim(Number(SPlus((int 17)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 128)(bol_pos 2935)(line_nb_last 128)(bol_pos_last 2935)(bp 2955)(ep 2957)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 128)(bol_pos 2935)(line_nb_last 128)(bol_pos_last 2935)(bp 2953)(ep 2957))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 128)(bol_pos 2935)(line_nb_last 128)(bol_pos_last 2935)(bp 2935)(ep 2971))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 19)(loc(((fname(InFile(dirpath)ufile))(line_nb 129)(bol_pos 2972)(line_nb_last 129)(bol_pos_last 2972)(bp 2981)(ep 2985))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 129)(bol_pos 2972)(line_nb_last 129)(bol_pos_last 2972)(bp 2990)(ep 2991)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 129)(bol_pos 2972)(line_nb_last 129)(bol_pos_last 2972)(bp 2990)(ep 2991)))))((((v(CPrim(Number(SPlus((int 18)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 129)(bol_pos 2972)(line_nb_last 129)(bol_pos_last 2972)(bp 2992)(ep 2994)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 129)(bol_pos 2972)(line_nb_last 129)(bol_pos_last 2972)(bp 2990)(ep 2994))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 129)(bol_pos 2972)(line_nb_last 129)(bol_pos_last 2972)(bp 2972)(ep 3008))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 20)(loc(((fname(InFile(dirpath)ufile))(line_nb 130)(bol_pos 3009)(line_nb_last 130)(bol_pos_last 3009)(bp 3018)(ep 3022))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 130)(bol_pos 3009)(line_nb_last 130)(bol_pos_last 3009)(bp 3027)(ep 3028)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 130)(bol_pos 3009)(line_nb_last 130)(bol_pos_last 3009)(bp 3027)(ep 3028)))))((((v(CPrim(Number(SPlus((int 19)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 130)(bol_pos 3009)(line_nb_last 130)(bol_pos_last 3009)(bp 3029)(ep 3031)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 130)(bol_pos 3009)(line_nb_last 130)(bol_pos_last 3009)(bp 3027)(ep 3031))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 130)(bol_pos 3009)(line_nb_last 130)(bol_pos_last 3009)(bp 3009)(ep 3045))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 21)(loc(((fname(InFile(dirpath)ufile))(line_nb 131)(bol_pos 3046)(line_nb_last 131)(bol_pos_last 3046)(bp 3055)(ep 3059))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 131)(bol_pos 3046)(line_nb_last 131)(bol_pos_last 3046)(bp 3064)(ep 3065)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 131)(bol_pos 3046)(line_nb_last 131)(bol_pos_last 3046)(bp 3064)(ep 3065)))))((((v(CPrim(Number(SPlus((int 20)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 131)(bol_pos 3046)(line_nb_last 131)(bol_pos_last 3046)(bp 3066)(ep 3068)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 131)(bol_pos 3046)(line_nb_last 131)(bol_pos_last 3046)(bp 3064)(ep 3068))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 131)(bol_pos 3046)(line_nb_last 131)(bol_pos_last 3046)(bp 3046)(ep 3082))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 22)(loc(((fname(InFile(dirpath)ufile))(line_nb 132)(bol_pos 3083)(line_nb_last 132)(bol_pos_last 3083)(bp 3092)(ep 3096))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 132)(bol_pos 3083)(line_nb_last 132)(bol_pos_last 3083)(bp 3101)(ep 3102)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 132)(bol_pos 3083)(line_nb_last 132)(bol_pos_last 3083)(bp 3101)(ep 3102)))))((((v(CPrim(Number(SPlus((int 21)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 132)(bol_pos 3083)(line_nb_last 132)(bol_pos_last 3083)(bp 3103)(ep 3105)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 132)(bol_pos 3083)(line_nb_last 132)(bol_pos_last 3083)(bp 3101)(ep 3105))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 132)(bol_pos 3083)(line_nb_last 132)(bol_pos_last 3083)(bp 3083)(ep 3119))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 23)(loc(((fname(InFile(dirpath)ufile))(line_nb 133)(bol_pos 3120)(line_nb_last 133)(bol_pos_last 3120)(bp 3129)(ep 3133))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 133)(bol_pos 3120)(line_nb_last 133)(bol_pos_last 3120)(bp 3138)(ep 3139)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 133)(bol_pos 3120)(line_nb_last 133)(bol_pos_last 3120)(bp 3138)(ep 3139)))))((((v(CPrim(Number(SPlus((int 22)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 133)(bol_pos 3120)(line_nb_last 133)(bol_pos_last 3120)(bp 3140)(ep 3142)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 133)(bol_pos 3120)(line_nb_last 133)(bol_pos_last 3120)(bp 3138)(ep 3142))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 133)(bol_pos 3120)(line_nb_last 133)(bol_pos_last 3120)(bp 3120)(ep 3156))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 24)(loc(((fname(InFile(dirpath)ufile))(line_nb 134)(bol_pos 3157)(line_nb_last 134)(bol_pos_last 3157)(bp 3166)(ep 3170))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id S)))(loc(((fname(InFile(dirpath)ufile))(line_nb 134)(bol_pos 3157)(line_nb_last 134)(bol_pos_last 3157)(bp 3175)(ep 3176)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 134)(bol_pos 3157)(line_nb_last 134)(bol_pos_last 3157)(bp 3175)(ep 3176)))))((((v(CPrim(Number(SPlus((int 23)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 134)(bol_pos 3157)(line_nb_last 134)(bol_pos_last 3157)(bp 3177)(ep 3179)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 134)(bol_pos 3157)(line_nb_last 134)(bol_pos_last 3157)(bp 3175)(ep 3179))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 134)(bol_pos 3157)(line_nb_last 134)(bol_pos_last 3157)(bp 3157)(ep 3193))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 100)(loc(((fname(InFile(dirpath)ufile))(line_nb 135)(bol_pos 3194)(line_nb_last 135)(bol_pos_last 3194)(bp 3203)(ep 3208))))))(ntn_decl_interp((v(CNotation(InConstrEntry"_ * _")((((v(CPrim(Number(SPlus((int 10)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 135)(bol_pos 3194)(line_nb_last 135)(bol_pos_last 3194)(bp 3213)(ep 3215)))))((v(CPrim(Number(SPlus((int 10)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 135)(bol_pos 3194)(line_nb_last 135)(bol_pos_last 3194)(bp 3218)(ep 3220)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 135)(bol_pos 3194)(line_nb_last 135)(bol_pos_last 3194)(bp 3213)(ep 3220))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 135)(bol_pos 3194)(line_nb_last 135)(bol_pos_last 3194)(bp 3194)(ep 3234))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v 1000)(loc(((fname(InFile(dirpath)ufile))(line_nb 136)(bol_pos 3235)(line_nb_last 136)(bol_pos_last 3235)(bp 3244)(ep 3250))))))(ntn_decl_interp((v(CNotation(InConstrEntry"_ * _")((((v(CPrim(Number(SPlus((int 10)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 136)(bol_pos 3235)(line_nb_last 136)(bol_pos_last 3235)(bp 3255)(ep 3257)))))((v(CPrim(Number(SPlus((int 100)(frac"")(exp""))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 136)(bol_pos 3235)(line_nb_last 136)(bol_pos_last 3235)(bp 3260)(ep 3263)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 136)(bol_pos 3235)(line_nb_last 136)(bol_pos_last 3235)(bp 3255)(ep 3263))))))(ntn_decl_scope(nat_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 136)(bol_pos 3235)(line_nb_last 136)(bol_pos_last 3235)(bp 3235)(ep 3277))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacInductive Inductive_kw((((NoCoercion(((v(Id paths))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3312)(ep 3317)))))))(((CLocalAssum(((v(Name(Id A)))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3319)(ep 3320))))))(Default MaxImplicit)((v(CRef((v(Ser_Qualid(DirPath)(Id UU)))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3321)(ep 3323)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3321)(ep 3323))))))(CLocalAssum(((v(Name(Id a)))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3326)(ep 3327))))))(Default Explicit)((v(CRef((v(Ser_Qualid(DirPath)(Id A)))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3328)(ep 3329)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3328)(ep 3329))))))))(((v(CNotation(InConstrEntry"_ -> _")((((v(CRef((v(Ser_Qualid(DirPath)(Id A)))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3333)(ep 3334)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3333)(ep 3334)))))((v(CRef((v(Ser_Qualid(DirPath)(Id UU)))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3338)(ep 3340)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3338)(ep 3340)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3333)(ep 3340))))))(Constructors(((NoCoercion NoInstance)(((v(Id paths_refl))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3344)(ep 3354)))))((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id paths)))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3357)(ep 3362)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3357)(ep 3362)))))((((v(CRef((v(Ser_Qualid(DirPath)(Id a)))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3363)(ep 3364)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3363)(ep 3364))))))(((v(CRef((v(Ser_Qualid(DirPath)(Id a)))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3365)(ep 3366)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3365)(ep 3366)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3357)(ep 3366)))))))))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 140)(bol_pos 3302)(line_nb_last 140)(bol_pos_last 3302)(bp 3302)(ep 3367))))) *)
(* ((v((control)(attrs(((v(global VernacFlagEmpty))(loc(((fname(InFile(dirpath)ufile))(line_nb 141)(bol_pos 3368)(line_nb_last 141)(bol_pos_last 3368)(bp 3370)(ep 3376)))))))(expr(VernacSynPure(VernacHints(core)(HintsResolve((((hint_priority)(hint_pattern))true(HintsReference((v(Ser_Qualid(DirPath)(Id paths_refl)))(loc(((fname(InFile(dirpath)ufile))(line_nb 142)(bol_pos 3378)(line_nb_last 142)(bol_pos_last 3378)(bp 3391)(ep 3401))))))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 141)(bol_pos 3368)(line_nb_last 142)(bol_pos_last 3378)(bp 3368)(ep 3410))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v"a = b")(loc(((fname(InFile(dirpath)ufile))(line_nb 143)(bol_pos 3411)(line_nb_last 143)(bol_pos_last 3411)(bp 3420)(ep 3427))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id paths)))(loc(((fname(InFile(dirpath)ufile))(line_nb 143)(bol_pos 3411)(line_nb_last 143)(bol_pos_last 3411)(bp 3432)(ep 3437)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 143)(bol_pos 3411)(line_nb_last 143)(bol_pos_last 3411)(bp 3432)(ep 3437)))))((((v(CRef((v(Ser_Qualid(DirPath)(Id a)))(loc(((fname(InFile(dirpath)ufile))(line_nb 143)(bol_pos 3411)(line_nb_last 143)(bol_pos_last 3411)(bp 3438)(ep 3439)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 143)(bol_pos 3411)(line_nb_last 143)(bol_pos_last 3411)(bp 3438)(ep 3439))))))(((v(CRef((v(Ser_Qualid(DirPath)(Id b)))(loc(((fname(InFile(dirpath)ufile))(line_nb 143)(bol_pos 3411)(line_nb_last 143)(bol_pos_last 3411)(bp 3440)(ep 3441)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 143)(bol_pos 3411)(line_nb_last 143)(bol_pos_last 3411)(bp 3440)(ep 3441)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 143)(bol_pos 3411)(line_nb_last 143)(bol_pos_last 3411)(bp 3432)(ep 3441))))))(ntn_decl_scope(type_scope))(ntn_decl_modifiers)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 143)(bol_pos 3411)(line_nb_last 143)(bol_pos_last 3411)(bp 3411)(ep 3456))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacSyntacticDefinition((v(Id idpath))(loc(((fname(InFile(dirpath)ufile))(line_nb 144)(bol_pos 3457)(line_nb_last 144)(bol_pos_last 3457)(bp 3466)(ep 3472)))))(((v(CRef((v(Ser_Qualid(DirPath)(Id paths_refl)))(loc(((fname(InFile(dirpath)ufile))(line_nb 144)(bol_pos 3457)(line_nb_last 144)(bol_pos_last 3457)(bp 3476)(ep 3486)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 144)(bol_pos 3457)(line_nb_last 144)(bol_pos_last 3457)(bp 3476)(ep 3486)))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 144)(bol_pos 3457)(line_nb_last 144)(bol_pos_last 3457)(bp 3457)(ep 3488))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacSetOption false(Primitive Projections)OptionSetTrue)))))(loc(((fname(InFile(dirpath)ufile))(line_nb 178)(bol_pos 5088)(line_nb_last 178)(bol_pos_last 5088)(bp 5088)(ep 5114))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacSetOption false(Nonrecursive Elimination Schemes)OptionSetTrue)))))(loc(((fname(InFile(dirpath)ufile))(line_nb 179)(bol_pos 5115)(line_nb_last 179)(bol_pos_last 5115)(bp 5115)(ep 5152))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacInductive Record((((NoCoercion(((v(Id total2))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5161)(ep 5167)))))))(((CLocalAssum(((v(Name(Id T)))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5170)(ep 5171))))))(Default MaxImplicit)((v(CRef((v(Ser_Qualid(DirPath)(Id UU)))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5173)(ep 5175)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5173)(ep 5175))))))(CLocalAssum(((v(Name(Id P)))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5180)(ep 5181))))))(Default Explicit)((v(CNotation(InConstrEntry"_ -> _")((((v(CRef((v(Ser_Qualid(DirPath)(Id T)))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5183)(ep 5184)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5183)(ep 5184)))))((v(CRef((v(Ser_Qualid(DirPath)(Id UU)))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5188)(ep 5190)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5188)(ep 5190)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5183)(ep 5190))))))))(RecordDecl(((v(Id tpair))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5196)(ep 5201))))))(((AssumExpr((v(Name(Id pr1)))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5204)(ep 5207)))))((v(CRef((v(Ser_Qualid(DirPath)(Id T)))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5210)(ep 5211)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5210)(ep 5211))))))((rfu_attrs)(rfu_coercion NoCoercion)(rfu_instance NoInstance)(rfu_priority)(rfu_notation)))((AssumExpr((v(Name(Id pr2)))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5213)(ep 5216)))))((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id P)))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5219)(ep 5220)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5219)(ep 5220)))))((((v(CRef((v(Ser_Qualid(DirPath)(Id pr1)))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5221)(ep 5224)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5221)(ep 5224)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5219)(ep 5224))))))((rfu_attrs)(rfu_coercion NoCoercion)(rfu_instance NoInstance)(rfu_priority)(rfu_notation)))))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 181)(bol_pos 5154)(line_nb_last 181)(bol_pos_last 5154)(bp 5154)(ep 5227))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacArguments((v(AN((v(Ser_Qualid(DirPath)(Id tpair)))(loc(((fname(InFile(dirpath)ufile))(line_nb 183)(bol_pos 5229)(line_nb_last 183)(bol_pos_last 5229)(bp 5239)(ep 5244)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 183)(bol_pos 5229)(line_nb_last 183)(bol_pos_last 5229)(bp 5239)(ep 5244)))))((RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status MaxImplicit)))(RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status Explicit)))(RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status Explicit)))(RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status Explicit)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 183)(bol_pos 5229)(line_nb_last 183)(bol_pos_last 5229)(bp 5229)(ep 5255))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacArguments((v(AN((v(Ser_Qualid(DirPath)(Id pr1)))(loc(((fname(InFile(dirpath)ufile))(line_nb 184)(bol_pos 5256)(line_nb_last 184)(bol_pos_last 5256)(bp 5266)(ep 5269)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 184)(bol_pos 5256)(line_nb_last 184)(bol_pos_last 5256)(bp 5266)(ep 5269)))))((RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status MaxImplicit)))(RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status MaxImplicit)))(RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status Explicit)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 184)(bol_pos 5256)(line_nb_last 184)(bol_pos_last 5256)(bp 5256)(ep 5278))))) *)
(* ((v((control)(attrs)(expr(VernacSynPure(VernacArguments((v(AN((v(Ser_Qualid(DirPath)(Id pr2)))(loc(((fname(InFile(dirpath)ufile))(line_nb 185)(bol_pos 5279)(line_nb_last 185)(bol_pos_last 5279)(bp 5289)(ep 5292)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 185)(bol_pos 5279)(line_nb_last 185)(bol_pos_last 5279)(bp 5289)(ep 5292)))))((RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status MaxImplicit)))(RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status MaxImplicit)))(RealArg((name Anonymous)(recarg_like false)(notation_scope)(implicit_status Explicit)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 185)(bol_pos 5279)(line_nb_last 185)(bol_pos_last 5279)(bp 5279)(ep 5301))))) *)
(* ((v((control)(attrs)(expr(VernacSynterp(VernacNotation false((ntn_decl_string((v"'∑'  x .. y , P")(loc(((fname(InFile(dirpath)ufile))(line_nb 187)(bol_pos 5303)(line_nb_last 187)(bol_pos_last 5303)(bp 5312)(ep 5331))))))(ntn_decl_interp((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id total2)))(loc(((fname(InFile(dirpath)ufile))(line_nb 187)(bol_pos 5303)(line_nb_last 187)(bol_pos_last 5303)(bp 5336)(ep 5342)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 187)(bol_pos 5303)(line_nb_last 187)(bol_pos_last 5303)(bp 5336)(ep 5342)))))((((v(CNotation(InConstrEntry"λ _ .. _ , _")((((v(CAppExpl(((v(Ser_Qualid(DirPath)(Id ..)))(loc(((fname(InFile(dirpath)ufile))(line_nb 187)(bol_pos 5303)(line_nb_last 187)(bol_pos_last 5303)(bp 5350)(ep 5374))))))(((v(CApp((v(CRef((v(Ser_Qualid(DirPath)(Id total2)))(loc(((fname(InFile(dirpath)ufile))(line_nb 187)(bol_pos 5303)(line_nb_last 187)(bol_pos_last 5303)(bp 5354)(ep 5360)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 187)(bol_pos 5303)(line_nb_last 187)(bol_pos_last 5303)(bp 5354)(ep 5360)))))((((v(CNotation(InConstrEntry"λ _ .. _ , _")((((v(CRef((v(Ser_Qualid(DirPath)(Id P)))(loc(((fname(InFile(dirpath)ufile))(line_nb 187)(bol_pos 5303)(line_nb_last 187)(bol_pos_last 5303)(bp 5368)(ep 5369)))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 187)(bol_pos 5303)(line_nb_last 187)(bol_pos_last 5303)(bp 5368)(ep 5369))))))(((CLocalAssum(((v(Name(Id y)))(loc(((fname(InFile(dirpath)ufile))(line_nb 187)(bol_pos 5303)(line_nb_last 187)(bol_pos_last 5303)(bp 5365)(ep 5366))))))(Default Explicit)((v(CHole((BinderType(Name(Id y))))IntroAnonymous))(loc(((fname(InFile(dirpath)ufile))(line_nb 187)(bol_pos 5303)(line_nb_last 187)(bol_pos_last 5303)(bp 5365)(ep 5366)))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 187)(bol_pos 5303)(line_nb_last 187)(bol_pos_last 5303)(bp 5362)(ep 5369)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 187)(bol_pos 5303)(line_nb_last 187)(bol_pos_last 5303)(bp 5354)(ep 5370))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 187)(bol_pos 5303)(line_nb_last 187)(bol_pos_last 5303)(bp 5350)(ep 5374))))))(((CLocalAssum(((v(Name(Id x)))(loc(((fname(InFile(dirpath)ufile))(line_nb 187)(bol_pos 5303)(line_nb_last 187)(bol_pos_last 5303)(bp 5347)(ep 5348))))))(Default Explicit)((v(CHole((BinderType(Name(Id x))))IntroAnonymous))(loc(((fname(InFile(dirpath)ufile))(line_nb 187)(bol_pos 5303)(line_nb_last 187)(bol_pos_last 5303)(bp 5347)(ep 5348)))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 187)(bol_pos 5303)(line_nb_last 187)(bol_pos_last 5303)(bp 5344)(ep 5374)))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 187)(bol_pos 5303)(line_nb_last 187)(bol_pos_last 5303)(bp 5336)(ep 5375))))))(ntn_decl_scope(type_scope))(ntn_decl_modifiers(((v(SetLevel 200))(loc(((fname(InFile(dirpath)ufile))(line_nb 188)(bol_pos 5377)(line_nb_last 188)(bol_pos_last 5377)(bp 5380)(ep 5392)))))((v(SetEntryType x(ETBinder true)))(loc(((fname(InFile(dirpath)ufile))(line_nb 188)(bol_pos 5377)(line_nb_last 188)(bol_pos_last 5377)(bp 5394)(ep 5402)))))((v(SetEntryType y(ETBinder true)))(loc(((fname(InFile(dirpath)ufile))(line_nb 188)(bol_pos 5377)(line_nb_last 188)(bol_pos_last 5377)(bp 5404)(ep 5412)))))((v(SetAssoc RightA))(loc(((fname(InFile(dirpath)ufile))(line_nb 188)(bol_pos 5377)(line_nb_last 188)(bol_pos_last 5377)(bp 5414)(ep 5433)))))))))))))(loc(((fname(InFile(dirpath)ufile))(line_nb 187)(bol_pos 5303)(line_nb_last 188)(bol_pos_last 5377)(bp 5303)(ep 5448))))) *)

Definition string_list : UU -> UU := list.
Definition string : UU := UU.
Definition MyUU := UU.
Inductive ast_desc : Type :=
| Adxu : ast_desc
| Ad_Ad_arg_label_expression_list_Da : ast_desc
| Ad_Ad_attributes_Da : ast_desc
| Ad_Ad_bool_Da : ast_desc
| Ad_Ad_empty_list_Da : ast_desc
| Ad_Ad_int_Da : ast_desc
| Ad_Ad_list : ast_desc
| Ad_Ad_loc2_Da : ast_desc
| Ad_Ad_loc_Da : ast_desc
| Ad_Ad_loc_stack_Da : ast_desc
| Ad_Ad_pos_Da : ast_desc
| Ad_Ad_process_arg_constructor_declaration_Da : ast_desc
| Ad_Ad_process_arg_label_expression_Da : ast_desc
| Ad_Ad_process_arg_label_expression_list_Da : ast_desc
| Ad_Ad_process_ast_desc : ast_desc
| Ad_Ad_process_cases : ast_desc
| Ad_Ad_process_cstrs_Da : ast_desc
| Ad_Ad_process_generic_list_Da : ast_desc
| Ad_Ad_process_label_declaration_list_Da : ast_desc
| Ad_Ad_process_list_tail_Da : ast_desc
| Ad_Ad_process_loc_Da : ast_desc
| Ad_Ad_process_params_Da : ast_desc
| Ad_Ad_process_string_loc_list_pattern_option_Da : ast_desc
| Ad_Ad_process_structure_item_Da : ast_desc
| Ad_Ad_process_structure_item_desc_Da : ast_desc
| Ad_Ad_process_structure_items_Da : ast_desc
| Ad_Ad_process_type_declaration_list_Da : ast_desc
| Ad_Ad_process_value_binding_list_Da : ast_desc
| Ad_Ad_process_var_list_Da : ast_desc
| Ad_Ad_quote_Da : ast_desc
| Ad_Definition : ast_desc
| Ad_FIXME : ast_desc
| Ad_FIXME_process_ast_desc : ast_desc
| Ad_Fixme1 : ast_desc
| Ad_Fixme2_Da : ast_desc
| Ad_Ident : ast_desc -> ast_desc
| Ad_MetaCoq_Definition : ast_desc
| Ad_NEW : ast_desc
| Ad_NoString : ast_desc
| Ad_Nolabel_Da : ast_desc
| Ad_None : ast_desc
| Ad_Nonrecursive_Da : ast_desc
| Ad_Obj : ast_desc
| Ad_P4 : ast_desc
| Ad_Pconst_string_Da : ast_desc
| Ad_Pexp_apply_Da : ast_desc
| Ad_Pexp_constant_Da : ast_desc
| Ad_Pexp_constraint_Da : ast_desc
| Ad_Pexp_construct_Da : ast_desc
| Ad_Pexp_fun_Da : ast_desc
| Ad_Pexp_ident_Da : ast_desc
| Ad_Pexp_tuple_Da : ast_desc
| Ad_Ppat_constraint_Da : ast_desc
| Ad_Ppat_var_Da : ast_desc
| Ad_Pstr_type_Da : ast_desc
| Ad_Pstr_value_Da : ast_desc
| Ad_Ptyp_constr_Da : ast_desc
| Ad_Ptype_abstract_Da : ast_desc
| Ad_Public_Da : ast_desc
| Ad_Recursive_Da : ast_desc
| Ad_String : ast_desc -> ast_desc(*orig*)
| Ad_TRUNCATED : ast_desc
| Ad_TypeParam_T : ast_desc
| Ad_TypeParam_T_dot : ast_desc
| Ad_Type_UU : ast_desc
| Ad_Da_Da : ast_desc
| Ad_Da_Da_Da : ast_desc
| Ad_ : ast_desc
| Ad_Da : ast_desc
| Ad_a_Da : ast_desc
| Ad_arg_label_Da : ast_desc
| Ad_arg_label_expression_list : ast_desc -> ast_desc(*orig*)
| Ad_ast_desc : ast_desc
| Ad_ast_desc_Da : ast_desc
| Ad_attributes : ast_desc(*orig*)
| Ad_b_Da : ast_desc
| Ad_bool : ast_desc -> ast_desc(*orig*)
| Ad_c_Da : ast_desc
| Ad_caret
| Ad_close_parens : ast_desc
| Ad_close_parens_Da_Da : ast_desc
| Ad_closebrace : ast_desc
| Ad_constant_Da : ast_desc
| Ad_core_type_desc_Da : ast_desc
| Ad_empty : ast_desc
| Ad_empty_array : ast_desc
| Ad_error : ast_desc
| Ad_errr : ast_desc
| Ad_expression_desc_Da : ast_desc
| Ad_fixme : ast_desc -> ast_desc(*orig*)
| Ad_foo1_Da : ast_desc
| Ad_ident_Da : ast_desc
| Ad_int : ast_desc -> ast_desc(*orig*)
| Ad_list : ast_desc -> ast_desc(*orig*)
| Ad_list_Da : ast_desc
| Ad_loc : ast_desc(*orig*)
| Ad_loc2 : ast_desc(*orig*)
| Ad_loc2_Da : ast_desc
| Ad_loc_Da : ast_desc
| Ad_loc_stack : ast_desc(*orig*)
| Ad_loc_stack_Da : ast_desc
| Ad_none_Da : ast_desc
| Ad_open_parenAd_Ident : ast_desc
| Ad_open_parenAd_String : ast_desc
| Ad_open_paren_rec_root : ast_desc
| Ad_openbrace
| Ad_pattern_desc_Da : ast_desc
| Ad_pos : ast_desc(*orig*)
| Ad_private_flag_Da : ast_desc
| Ad_process_arg_constructor_declaration : ast_desc -> ast_desc(*orig*)
| Ad_process_arg_constructor_declaration_Da : ast_desc
| Ad_process_arg_label_expression : ast_desc -> ast_desc -> ast_desc(*orig*)
| Ad_process_arg_label_expression_Da : ast_desc
| Ad_process_arg_label_expression_list : ast_desc -> ast_desc(*orig*)
| Ad_process_ast_desc : ast_desc -> ast_desc(*orig*)
| Ad_process_ast_desc_loc_list_pattern_option : ast_desc
| Ad_process_cases : ast_desc -> ast_desc(*orig*)
| Ad_process_core_type_list_Da : ast_desc
| Ad_process_cstrs : ast_desc -> ast_desc(*orig*)
| Ad_process_cstrs_Da : ast_desc
| Ad_process_expression_list_Da : ast_desc
| Ad_process_generic_list : ast_desc -> ast_desc -> ast_desc(*orig*)
| Ad_process_generic_type : ast_desc
| Ad_process_generic_type3
| Ad_process_generic_type_Da : ast_desc
| Ad_process_label_declaration_list : ast_desc -> ast_desc(*orig*)
| Ad_process_label_declaration_list_Da : ast_desc
| Ad_process_list_tail : ast_desc -> ast_desc -> ast_desc(*orig*)
| Ad_process_loc : ast_desc -> ast_desc(*orig*)
| Ad_process_loc_Da : ast_desc
| Ad_process_params : ast_desc -> ast_desc(*orig*)
| Ad_process_params_Da : ast_desc
| Ad_process_string : ast_desc
| Ad_process_string_loc_list_pattern_option : ast_desc(*orig*)
| Ad_process_string_loc_list_pattern_option_Da : ast_desc
| Ad_process_structure_item : ast_desc -> ast_desc(*orig*)
| Ad_process_structure_item_desc : ast_desc -> ast_desc(*orig*)
| Ad_process_structure_items : ast_desc -> ast_desc(*orig*)
| Ad_process_structure_items_Da : ast_desc
| Ad_process_type_declaration_list : ast_desc -> ast_desc(*orig*)
| Ad_process_type_declaration_list_Da : ast_desc
| Ad_process_value_binding_list : ast_desc(*orig*)
| Ad_process_var_list : ast_desc -> ast_desc(*orig*)
| Ad_process_vars_list_Da : ast_desc
| Ad_quot_list : ast_desc -> ast_desc
| Ad_quote : ast_desc -> ast_desc -> ast_desc(*orig*)
| Ad_rec_flag_Da : ast_desc
| Ad_root : ast_desc -> ast_desc(*orig*)
| Ad_string_Da : ast_desc
| Ad_structure_item_desc_Da : ast_desc
| Ad_todofixme : ast_desc
| Ad_type_kind_Da : ast_desc
| Ad_umcr_n_role_ : ast_desc
| Ad_umcr_n_type_ : ast_desc
| Ad_umcr_r_rel_ : ast_desc
| Ad_umcr_type : ast_desc
| Ad_x_Da : ast_desc
| Ad_y_Da : ast_desc
| ad_nostring : ast_desc
.

Inductive ast_desc_list  : Type :=
| Ad_empty_list : ast_desc_list
| Ad_cons : ast_desc ->ast_desc_list  ->ast_desc_list
.

(* Module simple_ast_root. *)
(*   Record record {sa_role sa_type sa_list : Set} : Set := Build { *)
(*     sa_role : sa_role; *)
(*     sa_type : sa_type; *)
(*     sa_list : sa_list; *)
(*   }. *)
(*   Arguments record : clear implicits. *)
(*   Definition with_sa_role {t_sa_role t_sa_type t_sa_list} sa_role *)
(*     (r : record t_sa_role t_sa_type t_sa_list) := *)
(*     Build t_sa_role t_sa_type t_sa_list sa_role r.(sa_type) r.(sa_list). *)
(*   Definition with_sa_type {t_sa_role t_sa_type t_sa_list} sa_type *)
(*     (r : record t_sa_role t_sa_type t_sa_list) := *)
(*     Build t_sa_role t_sa_type t_sa_list r.(sa_role) sa_type r.(sa_list). *)
(*   Definition with_sa_list {t_sa_role t_sa_type t_sa_list} sa_list *)
(*     (r : record t_sa_role t_sa_type t_sa_list) := *)
(*     Build t_sa_role t_sa_type t_sa_list r.(sa_role) r.(sa_type) sa_list. *)
(* End simple_ast_root. *)

(* Definition simple_ast_root_skeleton := simple_ast_root.record. *)

(*
ast_desc2 : Type
The term "simple_ast_root_skeleton" has type "Set → Set → Set → Set"
which should be Set, Prop or Type.

 Inductive ast_desc2 : Type := *)
(*   | Ad2_simple_ast_root_record : simple_ast_root_skeleton . *)



Definition ident (a_value : ast_desc) : ast_desc := Ad_Ident a_value.

Definition none : ast_desc := Ad_None.


Definition process_cases (x_value : ast_desc) : ast_desc :=
  Ad_process_cases x_value.

Definition process_var_list (x_value : ast_desc) : ast_desc :=
  Ad_process_var_list x_value.

Definition process_arg_constructor_declaration (x_value : ast_desc)
  : ast_desc := Ad_process_arg_constructor_declaration x_value.

Definition process_label_declaration_list (x_value : ast_desc)
  : ast_desc := Ad_process_label_declaration_list x_value.

Definition process_params (x_value : ast_desc) : ast_desc :=
  Ad_process_params x_value.

Definition process_cstrs (x_value : ast_desc) : ast_desc :=
  Ad_process_cstrs x_value.

Definition process_type_declaration_list (x_value : ast_desc) : ast_desc :=
  Ad_process_type_declaration_list x_value.

(* Definition loc : ast_desc := Ad_loc. *)

(* Definition loc2 : ast_desc := Ad_loc2. *)

(* Definition loc_stack : ast_desc := Ad_loc_stack. *)

(* Definition process_loc (a_value : ast_desc) : ast_desc := *)
(*   Ad_process_loc a_value. *)

(* Definition process_string_loc_list_pattern_option : ast_desc := *)
(*   Ad_process_string_loc_list_pattern_option. *)

(* Definition process_arg_label_expression *)
(*   (x_value : ast_desc) (y_value : ast_desc) : ast_desc := *)
(*   Ad_process_arg_label_expression x_value y_value. *)

(* Definition process_expression_list (x_value : ast_desc) : ast_desc := *)
(*   Ad_arg_label_expression_list x_value. *)

(* Definition process_arg_label_expression_list (a_value : ast_desc) *)
(*   : ast_desc := Ad_process_arg_label_expression_list a_value. *)

(* Definition process_location (a_value : ast_desc) : ast_desc := *)
(*   Ad_process_loc a_value. *)

(* Definition process_location_stack (a_value : ast_desc) : ast_desc := *)
(*   Ad_process_loc a_value. *)

(* Definition attributes : ast_desc := Ad_attributes. *)

(* Definition process_value_binding_list : ast_desc := *)
(*   Ad_process_value_binding_list. *)

(* Definition pos (a_value : ast_desc) : ast_desc := Ad_process_loc a_value. *)

(* Definition b_value (a_value : ast_desc) : ast_desc := Ad_bool a_value. *)

(* Definition mint (a_value : ast_desc) : ast_desc := Ad_int a_value. *)

(* Definition string_value (a_value : ast_desc) : ast_desc := Ad_String a_value. *)

(* Definition make_pair (a_value : ast_desc) (b_value : ast_desc) : ast_desc := Ad_None. *)

(* Definition process_string_option : ast_desc := Ad_NoString. *)

(* Notation "[ a , b ]" := (make_pair a b ). *)

(* Definition process_structure_items (x_value : ast_desc) : ast_desc := *)
(*   Ad_process_structure_items x_value. *)



(* (* Fixpoint process_generic_list_tail *) *)
(* (*   (name : ast_desc) (a_value :   ast_desc_list  ) (f_value : ast_desc -> ast_desc) *) *)
(* (*   : ast_desc_list := *) *)
(* (*   match a_value with *) *)

(* (*   | Ad_empty_list => Ad_empty_list *) *)
(* (*   | Ad_cons a_value t_value => *) *)
(* (*     let v1 := f_value a_value in Ad_empty_list *) *)
(* (*     (* if Stdlib.not_empty t_value nil then *) *) *)
(* (*     (*   Ad_process_list_tail v1 (process_generic_list_tail name t_value f_value) *) *) *)
(* (*     (* else *) *) *)
(* (*     (*   v1 *) *) *)
(* (*   end *) *)

(* Definition  my_append (a_value : ast_desc) (b_value : ast_desc) : ast_desc := a_value . *)

(* Definition process_generic_type3 *)
(*   (a_value : ast_desc) (b_value : ast_desc) (c_value : ast_desc) : ast_desc := *)
(*   my_append Ad_process_generic_type3 *)
(*     (my_append a_value *)
(*       (my_append Ad_caret *)
(*         (my_append b_value *)
(*           (my_append Ad_openbrace *)
(*             (my_append Ad_None(* (process_ast_desc4  c_value) *) Ad_closebrace ))))) *)
(* . *)

(* Definition quot (a_value : ast_desc) (b_value : ast_desc) : ast_desc := *)
(*   Ad_quote a_value b_value *)
(* . *)

(* Definition ad_list(ls : ast_desc_list) := *)
(*   Ad_list Ad_None *)
(* . *)

(* Definition quot_list (n_value : ast_desc) (fn : ast_desc -> ast_desc) (ls : ast_desc_list) *)
(*   : ast_desc := *)
(*   let quot_a (c_value : ast_desc) : ast_desc := *)
(*     quot n_value (fn c_value) in *)
(*   Ad_None *)
(*   (* process_generic_list (my_append (Ad_quot_list n_value (ad_list ls) quot_a)) *) *)
(* . *)

(* Definition process_ast_desc (l_value : ast_desc) : ast_desc := *)
(*   Ad_fixme Ad_FIXME_process_ast_desc *)
(* . *)

(* Definition process_simple_ast_root (x_value : ast_desc) : ast_desc := *)
(*   Ad_root x_value *)
(* . *)

(* Definition process_string (a_value : ast_desc) : ast_desc := *)
(*   quot Ad_process_string a_value *)
(* . *)

(* Definition process_int (a_value : ast_desc) : ast_desc := Ad_int a_value *)
(* . *)

(* Definition process_bool (a_value : ast_desc) : ast_desc := Ad_bool a_value *)
(* . *)

(* Definition process_generic_list *)
(*   (name : ast_desc) (a_value : ast_desc_list) (f_value : ast_desc -> ast_desc) *)
(*   : ast_desc := name. *)

(*   (* Ad_process_generic_list name *) *)
(*   (*   [ *) *)
(*   (*     match a_value with *) *)
(*   (*     | Ad_empty_list => Ad_empty_list name *) *)
(*   (*     | cons a_value t_value => *) *)
(*   (*       let v1 := f_value a_value in *) *)
(*   (*       if Stdlib.not_empty t_value nil then *) *)
(*   (*         Ad_process_list_tail v1 *) *)
(*   (*           (process_generic_list_tail name t_value f_value) *) *)
(*   (*       else *) *)
(*   (*         v1 *) *)
(*   (*     end *) *)
(*   (*   ] *) *)
(* Definition print_endline (a:ast_desc):unit := tt. *)


(* (*TODO in coq return unit*) *)
(* Definition def_basic (a_value : ast_desc) (b_value : ast_desc) : ast_desc := *)
(*   let t_value := *)
(*     my_append Ad_MetaCoq_Definition *)
(*       (my_append a_value *)
(*         (my_append Ad_TypeParam_T (my_append b_value Ad_Type_UU))) *)
(*     in *)
(*   let '_ := print_endline t_value in *)
(*   t_value *)
(* . *)

(* Definition def_pair (a_value : ast_desc) (b_value : ast_desc) (a1 : ast_desc) (b1 : ast_desc) *)
(*   : ast_desc := *)
(*   let tt := *)
(*     my_append Ad_Definition *)
(*       (my_append a_value *)
(*         (my_append Ad_TypeParam_T *)
(*           (my_append b_value *)
(*             (my_append Ad_Type_UU *)
(*               (my_append a1 *)
(*                 (my_append Adxu (my_append b1 Ad_TypeParam_T_dot ))))))) in *)
(*   let '_ := print_endline tt in *)
(*   tt *)
(* . *)

(* Definition process_generic_type2 {A : MyUU} *)
(*   (a_value : ast_desc) (b_value : ast_desc) (c_value : A) : ast_desc := Ad_empty *)
(*   (* let baset := Ad_umcr_type in *) *)
(*   (* let _at := my_append Ad_umcr_n_role_ a_value in *) *)
(*   (* let bt := my_append Ad_umcr_n_type_ b_value in *) *)
(*   (* let ct := *) *)
(*   (*   my_append Ad_umcr_r_rel_ *) *)
(*   (*     (my_append a_value (my_append Ad_ b_value)) in *) *)
(*   (* let f1 := def_basic _at baset in *) *)
(*   (* let f2 := def_basic bt baset in *) *)
(*   (* let f3 := def_pair ct baset _at bt in *) *)
(*   (* my_append Ad_ (my_append f1 (my_append f2 f3)) *) *)
(* . *)

(* (* Definition process_ast_desc (x_value : ast_desc) : ast_desc := *) *)
(* (*   Ad_fixme Ad_Ad_process_ast_desc *) *)
(* (* . *) *)

(* Definition not_empty (al : ast_desc_list) : bool := false *)
(* . *)
(* Definition ast_dest_list_to_single (al : ast_desc_list) : ast_desc := Ad_empty *)
(* . *)
(* Definition process_ast_desc3 (al : ast_desc_list) : ast_desc := Ad_empty *)
(*                                                              . *)
(* Definition process_ast_desc4 (al : ast_desc) : ast_desc := Ad_empty *)
(* . *)
(*                                          Definition process_ast_desc2 (al : ast_desc_list) : ast_desc := *)
(*   match al with *)
(*   | Ad_empty_list => Ad_empty *)
(*   | Ad_cons h_value t_value => *)
(*     if not_empty t_value  then *)
(*       (* my_append (extract_root h_value) *) *)
(*       (*   (my_append Ad_caret (process_ast_desc3 t_value)) *) *)
(*       Ad_FIXME *)
(*     else *)
(*       Ad_empty_array *)
(*   end *)
(* . *)
(* (* Definition extract_root (al : ast_desc) : ast_desc := al. *) *)
(* (* Definition process_ast_desc3 (al : ast_desc_list) : ast_desc := *) *)
(* (*   match al with *) *)
(* (*   | Ad_empty_list => Ad_empty *) *)
(* (*   | Ad_cons h_value t_value => *) *)
(* (*     if not_empty t_value  then *) *)
(* (*       my_append (extract_root h_value) *) *)
(* (*         (my_append Ad_caret (process_ast_desc3 t_value)) *) *)
(* (*     else *) *)
(* (*       Ad_error *) *)
(* (*   end *)
(* . *)
(*  *) *)


(* (* Definition process_ast_desc4 (al : ast_desc_list) : ast_desc := *) *)
(* (*   match al with *) *)
(* (*   | Ad_empty_list => Ad_empty *) *)
(* (*   | Ad_cons h_value t_value => *) *)
(* (*     if not_empty t_value then *) *)
(* (*       my_append (extract_root h_value) (my_append Ad_caret Ad_TRUNCATED) *) *)
(* (*     else *) *)
(* (*        Ad_errr *) *)
(* (*   end *) *)
(* (* . *) *)

(* Definition process_root_list (a_value : ast_desc) : ast_desc := a_value *)
(*   (* match a_value with *) *)
(*   (* | Ad_empty_list => Ad_empty *) *)
(*   (* | Ad_cons x_value t_value => *) *)
(*   (*   let v1 := extract_root x_value in *) *)
(*   (*   if not_empty t_value  then *) *)
(*   (*     my_append v1 (my_append Ad_caret (process_root_list t_value)) *) *)
(*   (*   else *) *)
(*   (*     v1 *) *)
(*   (* end *) *)
(* . *)

(* Definition tostring (x_value : ast_desc) : ast_desc := Ad_todofixme *)
(* . *)

(* Definition ast_desc_to_yojson (x_value : ast_desc) : ast_desc := *)
(*   x_value *)
(* . *)

(* Definition process_generic_type_print *)
(*   (a_value : ast_desc) (b_value : ast_desc) (c_value : ast_desc) : unit := *)
(*   let yj := tostring (ast_desc_to_yojson c_value) in *)
(*   let dd := my_append Ad_process_generic_type (my_append a_value b_value) *)
(*     in *)
(*   let yj1 := process_root_list c_value in *)
(*   let '_ := print_endline yj in *)
(*   let '_ := print_endline dd in *)
(*   print_endline (my_append Ad_NEW yj1) *)
(* . *)

(* Definition process_generic_type *)
(*   (a_value : ast_desc) (b_value : ast_desc) (c_value : ast_desc) : ast_desc := *)
(*   let '_ := process_generic_type_print a_value b_value c_value in *)
(*   Ad_None *)
(*     (* Ad2_simple_ast_root_record {| simple_ast_root.sa_role := a_value; simple_ast_root.sa_type := b_value; *) *)
(*     (*   simple_ast_root.sa_list := c_value; |} *) *)
(* . *)

(* Definition process_structure_item (x_value : ast_desc) : ast_desc := *)
(*   Ad_process_structure_item x_value *)
(* . *)

(* Definition process_structure_item_desc (x_value : ast_desc) : ast_desc := *)
(*   Ad_process_structure_item_desc x_value *)
(* . *)

(* (* Definition process_structure_items (x_value : ast_desc_list) : ast_desc := *) *)
(* (*   process_generic_list Ad_Ad_process_structure_items_Da x_value process_structure_item. *) *)

(* Definition extract_root (x_value : ast_desc) : ast_desc := *)
(*   match x_value with *)
(*   | Ad_Ad_arg_label_expression_list_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_attributes_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_bool_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_empty_list_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_int_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_list     => Ad_Fixme1 *)
(*   | Ad_Ad_loc2_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_loc_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_loc_stack_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_pos_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_process_arg_constructor_declaration_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_process_arg_label_expression_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_process_arg_label_expression_list_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_process_ast_desc => Ad_Fixme1 *)
(*   | Ad_Ad_process_cases     => Ad_Fixme1 *)
(*   | Ad_Ad_process_cstrs_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_process_generic_list_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_process_label_declaration_list_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_process_list_tail_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_process_loc_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_process_params_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_process_string_loc_list_pattern_option_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_process_structure_item_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_process_structure_item_desc_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_process_structure_items_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_process_type_declaration_list_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_process_value_binding_list_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_process_var_list_Da     => Ad_Fixme1 *)
(*   | Ad_Ad_quote_Da     => Ad_Fixme1 *)
(*   | Ad_Definition     => Ad_Fixme1 *)
(*   | Ad_FIXME *)
(*   | Ad_FIXME_process_ast_desc *)
(*   | Ad_Fixme1     => Ad_Fixme1 *)
(*   | Ad_Fixme2_Da     => Ad_Fixme1 *)
(*   | Ad_Ident string0 =>   Ad_Ident string0 *)
(*   | Ad_MetaCoq_Definition     => Ad_Fixme1 *)
(*   | Ad_NEW     => Ad_Fixme1 *)
(*   | Ad_NoString => Ad_Fixme1 *)
(*   | Ad_Nolabel_Da     => Ad_Fixme1 *)
(*   | Ad_None => Ad_Fixme1 *)
(*   | Ad_Nonrecursive_Da     => Ad_Fixme1 *)
(*   | Ad_Obj     => Ad_Fixme1 *)
(*   | Ad_P4     => Ad_Fixme1 *)
(*   | Ad_Pconst_string_Da     => Ad_Fixme1 *)
(*   | Ad_Pexp_apply_Da     => Ad_Fixme1 *)
(*   | Ad_Pexp_constant_Da     => Ad_Fixme1 *)
(*   | Ad_Pexp_constraint_Da     => Ad_Fixme1 *)
(*   | Ad_Pexp_construct_Da     => Ad_Fixme1 *)
(*   | Ad_Pexp_fun_Da     => Ad_Fixme1 *)
(*   | Ad_Pexp_ident_Da     => Ad_Fixme1 *)
(*   | Ad_Pexp_tuple_Da     => Ad_Fixme1 *)
(*   | Ad_Ppat_constraint_Da     => Ad_Fixme1 *)
(*   | Ad_Ppat_var_Da     => Ad_Fixme1 *)
(*   | Ad_Pstr_type_Da     => Ad_Fixme1 *)
(*   | Ad_Pstr_value_Da     => Ad_Fixme1 *)
(*   | Ad_Ptyp_constr_Da     => Ad_Fixme1 *)
(*   | Ad_Ptype_abstract_Da     => Ad_Fixme1 *)
(*   | Ad_Public_Da     => Ad_Fixme1 *)
(*   | Ad_Recursive_Da     => Ad_Fixme1 *)
(*   | Ad_String string0 =>   Ad_Fixme1 *)
(*   | Ad_TRUNCATED     => Ad_Fixme1 *)
(*   | Ad_TypeParam_T     => Ad_Fixme1 *)
(*   | Ad_TypeParam_T_dot     => Ad_Fixme1 *)
(*   | Ad_Type_UU     => Ad_Fixme1 *)
(*   | Ad_Da_Da     => Ad_Fixme1 *)
(*   | Ad_Da_Da_Da     => Ad_Fixme1 *)
(*   | Ad_     => Ad_Fixme1 *)
(*   | Ad_Da     => Ad_Fixme1 *)
(*   | Ad_a_Da     => Ad_Fixme1 *)
(*   | Ad_arg_label_Da     => Ad_Fixme1 *)
(*   | Ad_arg_label_expression_list ast_desc0 =>    Ad_Fixme1 *)
(*   | Ad_ast_desc     => Ad_Fixme1 *)
(*   | Ad_ast_desc_Da     => Ad_Fixme1 *)
(*   | Ad_attributes => Ad_Fixme1 *)
(*   | Ad_b_Da     => Ad_Fixme1 *)
(*   | Ad_bool bool0 =>    Ad_bool bool0 *)
(*   | Ad_c_Da     => Ad_Fixme1 *)
(*   | Ad_caret *)
(*   | Ad_close_parens     => Ad_Fixme1 *)
(*   | Ad_close_parens_Da_Da     => Ad_Fixme1 *)
(*   | Ad_closebrace     => Ad_Fixme1 *)
(*   | Ad_constant_Da     => Ad_Fixme1 *)
(*   | Ad_core_type_desc_Da     => Ad_Fixme1 *)
(*   | Ad_empty     => Ad_Fixme1 *)
(*   | Ad_empty_array     => Ad_Fixme1 *)
(*   | Ad_error     => Ad_Fixme1 *)
(*   | Ad_errr     => Ad_Fixme1 *)
(*   | Ad_expression_desc_Da     => Ad_Fixme1 *)
(*   | Ad_fixme  _   => Ad_Fixme1 *)
(*   | Ad_foo1_Da     => Ad_Fixme1 *)
(*   | Ad_ident_Da     => Ad_Fixme1 *)
(*   | Ad_int int0 =>  Ad_Fixme1 *)
(*   | Ad_list  _   => Ad_Fixme1 *)

(*   | Ad_list_Da     => Ad_Fixme1 *)
(*   | Ad_loc => process_generic_type3 Ad_ast_desc_Da Ad_Ad_loc_Da Ad_None *)
(*   | Ad_loc2 => process_generic_type3 Ad_ast_desc_Da Ad_Ad_loc2_Da Ad_None *)
(*   | Ad_loc2_Da     => Ad_Fixme1 *)
(*   | Ad_loc_Da     => Ad_Fixme1 *)
(*   | Ad_loc_stack => process_generic_type3 Ad_ast_desc_Da Ad_Ad_loc_stack_Da Ad_None *)
(*   | Ad_loc_stack_Da     => Ad_Fixme1 *)
(*   | Ad_none_Da     => Ad_Fixme1 *)
(*   | Ad_open_parenAd_Ident     => Ad_Fixme1 *)
(*   | Ad_open_parenAd_String     => Ad_Fixme1 *)
(*   | Ad_open_paren_rec_root     => Ad_Fixme1 *)
(*   | Ad_openbrace *)
(*   | Ad_pattern_desc_Da     => Ad_Fixme1 *)
(*   | Ad_pos => process_generic_type3 Ad_ast_desc_Da Ad_Ad_pos_Da Ad_None *)
(*   | Ad_private_flag_Da     => Ad_Fixme1 *)

(*   | Ad_process_arg_constructor_declaration ast_desc0 =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_arg_constructor_declaration_Da      (Ad_process_ast_desc ast_desc0) *)
(*   | Ad_process_arg_constructor_declaration_Da     => Ad_Fixme1 *)

(*   | Ad_process_arg_label_expression ast_desc0 ast_desc1 =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_arg_label_expression_Da      [ process_ast_desc ast_desc0, process_ast_desc ast_desc1 ] *)
(*   | Ad_process_arg_label_expression_Da     => Ad_Fixme1 *)

(*   | Ad_process_arg_label_expression_list ast_desc0 =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_arg_label_expression_list_Da      (Ad_process_ast_desc ast_desc0) *)
(*   | Ad_process_ast_desc _ => Ad_Fixme2_Da *)
(*   | Ad_process_ast_desc_loc_list_pattern_option     => Ad_Fixme1 *)

(*   | Ad_process_cases ast_desc0 =>    process_generic_type3 Ad_ast_desc Ad_Ad_process_cases      (Ad_process_ast_desc ast_desc0) *)
(*   | Ad_process_core_type_list_Da     => Ad_Fixme1 *)

(*   | Ad_process_cstrs ast_desc0 =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_cstrs_Da     (Ad_process_ast_desc ast_desc0) *)
(*   | Ad_process_cstrs_Da     => Ad_Fixme1 *)
(*   | Ad_process_expression_list_Da     => Ad_Fixme1 *)

(*   | Ad_process_generic_list string0 ast_desc1 =>     process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_generic_list_Da      [        process_string string0,        Ad_fixme Ad_P4      ] *)
(*   | Ad_process_generic_type     => Ad_Fixme1 *)
(*   | Ad_process_generic_type3 *)
(*   | Ad_process_generic_type_Da     => Ad_Fixme1 *)

(*   | Ad_process_label_declaration_list ast_desc0 =>    (* process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_label_declaration_list_Da    Ad_Ad_process_ast_desc ast_desc0 *) Ad_FIXME *)
(*   | Ad_process_label_declaration_list_Da     => Ad_Fixme1 *)

(*   | Ad_process_list_tail ast_desc0 ast_desc1 =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_list_tail_Da      [ process_ast_desc ast_desc0, process_ast_desc ast_desc1 ] *)

(*   | Ad_process_loc ast_desc0 =>    (* process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_loc_Da        process_ast_desc ast_desc0 *) Ad_Fixme1 *)
(*   | Ad_process_loc_Da     => Ad_Fixme1 *)

(*   | Ad_process_params ast_desc0 => Ad_Fixme1 (*    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_params_Da       process_ast_desc ast_desc0 *) *)
(*   | Ad_process_params_Da     => Ad_Fixme1 *)
(*   | Ad_process_string     => Ad_Fixme1 *)
(*   | Ad_process_string_loc_list_pattern_option =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_string_loc_list_pattern_option_Da       Ad_None *)
(*   | Ad_process_string_loc_list_pattern_option_Da     => Ad_Fixme1 *)
(*   | Ad_process_structure_item _    => Ad_Fixme1 *)
(*   (* | Ad_process_structure_item ast_desc0 =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_structure_item_Da      process_ast_desc ast_desc0 *) *)
(*   | Ad_process_structure_item_desc _    => Ad_Fixme1 *)
(*   (* | Ad_process_structure_item_desc ast_desc0 =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_structure_item_desc_Da      process_ast_desc ast_desc0 *) *)
(*   | Ad_process_structure_items  _   => Ad_Fixme1 *)
(*   (* | Ad_process_structure_items ast_desc0 =>      process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_structure_items_Da       process_ast_desc ast_desc0 *) *)
(*   | Ad_process_structure_items_Da     => Ad_Fixme1 *)
(*   | Ad_process_type_declaration_list _    => Ad_Fixme1 *)
(*   (* | Ad_process_type_declaration_list ast_desc0 =>     process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_type_declaration_list_Da        process_ast_desc ast_desc0 *) *)
(*   | Ad_process_type_declaration_list_Da     => Ad_Fixme1 *)
(*   | Ad_process_value_binding_list =>     process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_value_binding_list_Da Ad_None *)
(*   | Ad_process_var_list   _  => Ad_Fixme1 *)
(*   (* | Ad_process_var_list ast_desc0 =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_var_list_Da      process_ast_desc ast_desc0 *) *)
(*   | Ad_process_vars_list_Da     => Ad_Fixme1 *)
(*   | Ad_quot_list  _   => Ad_Fixme1 *)
(*   | Ad_quote  _ _   => Ad_Fixme1 *)
(*   (* | Ad_quote string0 ast_desc1 =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_quote_Da      [ process_string string0, process_string ast_desc1 ] *) *)
(*   | Ad_rec_flag_Da     => Ad_Fixme1 *)
(*   | Ad_root  _   => Ad_Fixme1 *)
(*   | Ad_string_Da     => Ad_Fixme1 *)
(*   | Ad_structure_item_desc_Da     => Ad_Fixme1 *)
(*   | Ad_todofixme     => Ad_Fixme1 *)
(*   | Ad_type_kind_Da     => Ad_Fixme1 *)
(*   | Ad_umcr_n_role_     => Ad_Fixme1 *)
(*   | Ad_umcr_n_type_     => Ad_Fixme1 *)
(*   | Ad_umcr_r_rel_     => Ad_Fixme1 *)
(*   | Ad_umcr_type     => Ad_Fixme1 *)
(*   | Ad_x_Da     => Ad_Fixme1 *)
(*   | Ad_y_Da     => Ad_Fixme1 *)
(*   | Adxu => Ad_Fixme1 *)
(*   | ad_nostring     => Ad_Fixme1 *)

(*   end. *)

(* Definition ff1 := process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da ( string_value Ad_none_Da ). *)
(* Definition ff0 := process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None. *)


(* Definition ff00 :=      Ad_None. *)

(* Definition ff000 :=     (process_generic_type Ad_constant_Da Ad_Pconst_string_Da            ff00). *)
(* Definition ff2 := process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *)
(*         ff000. *)

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       ff0, *)
(*       [ *)
(*         ff1, *)
(*         ff2 *)
(*       ] *)
(*     ]. *)

(* (* Definition foo1 : ast_desc := *) *)
(* (*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *) *)
(* (*     [ *) *)
(* (*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *) *)
(* (*       [ *) *)
(* (*       (process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*         (string_value Ad_process_vars_list_Da)) *) *)
(* (*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *) *)
(* (*         [ *) *)
(* (*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *) *)
(* (*           none, *) *)
(* (*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*             string_value Ad_x_Da , *) *)
(* (*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *) *)
(* (*             [ *) *)
(* (*               process_generic_type Ad_constant_Da *) *)
(* (*                 Ad_Pconst_string_Da *) *)
(* (*                 [ *) *)
(* (*                   string_value *) *)
(* (*                     Ad_process_vars_list_Da, *) *)
(* (*                   process_string_option *) *)
(* (*                 ] *) *)
(* (*             ] *) *)
(* (*         ] *) *)
(* (*     ]. *) *)

(* (* Definition foo1 : ast_desc := *) *)
(* (*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *) *)
(* (*     [ *) *)
(* (*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *) *)
(* (*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*         [ string_value Ad_process_arg_constructor_declaration_Da ], *) *)
(* (*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *) *)
(* (*         [ *) *)
(* (*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *) *)
(* (*           none, *) *)
(* (*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*             [ string_value Ad_x_Da ], *) *)
(* (*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *) *)
(* (*             [ *) *)
(* (*               process_generic_type Ad_constant_Da *) *)
(* (*                 Ad_Pconst_string_Da *) *)
(* (*                 [ *) *)
(* (*                   string_value *) *)
(* (*                     Ad_process_arg_constructor_declaration_Da, *) *)
(* (*                   process_string_option *) *)
(* (*                 ] *) *)
(* (*             ] *) *)
(* (*         ] *) *)
(* (*     ]. *) *)

(* (* Definition foo1 : ast_desc := *) *)
(* (*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *) *)
(* (*     [ *) *)
(* (*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *) *)
(* (*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*         [ string_value Ad_process_label_declaration_list_Da ], *) *)
(* (*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *) *)
(* (*         [ *) *)
(* (*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *) *)
(* (*           none, *) *)
(* (*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*             [ string_value Ad_x_Da ], *) *)
(* (*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *) *)
(* (*             [ *) *)
(* (*               process_generic_type Ad_constant_Da *) *)
(* (*                 Ad_Pconst_string_Da *) *)
(* (*                 [ *) *)
(* (*                   string_value *) *)
(* (*                     Ad_process_label_declaration_list_Da, *) *)
(* (*                   process_string_option *) *)
(* (*                 ] *) *)
(* (*             ] *) *)
(* (*         ] *) *)
(* (*     ]. *) *)

(* (* Definition foo1 : ast_desc := *) *)
(* (*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *) *)
(* (*     [ *) *)
(* (*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *) *)
(* (*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*         [ string_value Ad_process_params_Da ], *) *)
(* (*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *) *)
(* (*         [ *) *)
(* (*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *) *)
(* (*           none, *) *)
(* (*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*             [ string_value Ad_x_Da ], *) *)
(* (*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *) *)
(* (*             [ *) *)
(* (*               process_generic_type Ad_constant_Da *) *)
(* (*                 Ad_Pconst_string_Da *) *)
(* (*                 [ *) *)
(* (*                   string_value *) *)
(* (*                     Ad_process_params_Da, *) *)
(* (*                   process_string_option *) *)
(* (*                 ] *) *)
(* (*             ] *) *)
(* (*         ] *) *)
(* (*     ]. *) *)

(* (* Definition foo1 : ast_desc := *) *)
(* (*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *) *)
(* (*     [ *) *)
(* (*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *) *)
(* (*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*         [ string_value Ad_process_cstrs_Da ], *) *)
(* (*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *) *)
(* (*         [ *) *)
(* (*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *) *)
(* (*           none, *) *)
(* (*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*             [ string_value Ad_x_Da ], *) *)
(* (*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *) *)
(* (*             [ *) *)
(* (*               process_generic_type Ad_constant_Da *) *)
(* (*                 Ad_Pconst_string_Da *) *)
(* (*                 [ *) *)
(* (*                   string_value *) *)
(* (*                     Ad_process_cstrs_Da, *) *)
(* (*                   process_string_option *) *)
(* (*                 ] *) *)
(* (*             ] *) *)
(* (*         ] *) *)
(* (*     ]. *) *)

(* (* Definition foo1 : ast_desc := *) *)
(* (*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *) *)
(* (*     [ *) *)
(* (*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *) *)
(* (*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*         [ string_value Ad_process_core_type_list_Da ], *) *)
(* (*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *) *)
(* (*         [ *) *)
(* (*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *) *)
(* (*           none, *) *)
(* (*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*             [ string_value Ad_x_Da ], *) *)
(* (*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *) *)
(* (*             [ *) *)
(* (*               process_generic_type Ad_constant_Da *) *)
(* (*                 Ad_Pconst_string_Da *) *)
(* (*                 [ *) *)
(* (*                   string_value *) *)
(* (*                     Ad_process_core_type_list_Da, *) *)
(* (*                   process_string_option *) *)
(* (*                 ] *) *)
(* (*             ] *) *)
(* (*         ] *) *)
(* (*     ]. *) *)

(* (* Definition foo1 : ast_desc := *) *)
(* (*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *) *)
(* (*     [ *) *)
(* (*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *) *)
(* (*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*         [ string_value Ad_process_type_declaration_list_Da ], *) *)
(* (*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *) *)
(* (*         [ *) *)
(* (*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *) *)
(* (*           none, *) *)
(* (*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*             [ string_value Ad_x_Da ], *) *)
(* (*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *) *)
(* (*             [ *) *)
(* (*               process_generic_type Ad_constant_Da *) *)
(* (*                 Ad_Pconst_string_Da *) *)
(* (*                 [ *) *)
(* (*                   string_value *) *)
(* (*                     Ad_process_type_declaration_list_Da, *) *)
(* (*                   process_string_option *) *)
(* (*                 ] *) *)
(* (*             ] *) *)
(* (*         ] *) *)
(* (*     ]. *) *)

(* (* Definition foo1 : ast_desc := *) *)
(* (*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *) *)
(* (*     [ *) *)
(* (*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *) *)
(* (*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da [ string_value Ad_loc_Da ], *) *)
(* (*       process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *) *)
(* (*         [ *) *)
(* (*           process_generic_type Ad_constant_Da Ad_Pconst_string_Da *) *)
(* (*             [ string_value Ad_loc_Da, process_string_option ] *) *)
(* (*         ] *) *)
(* (*     ]. *) *)

(* (* Definition foo1 : ast_desc := *) *)
(* (*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *) *)
(* (*     [ *) *)
(* (*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *) *)
(* (*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da [ string_value Ad_loc2_Da ], *) *)
(* (*       process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *) *)
(* (*         [ *) *)
(* (*           process_generic_type Ad_constant_Da Ad_Pconst_string_Da *) *)
(* (*             [ string_value Ad_loc_Da, process_string_option ] *) *)
(* (*         ] *) *)
(* (*     ]. *) *)

(* (* Definition foo1 : ast_desc := *) *)
(* (*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *) *)
(* (*     [ *) *)
(* (*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *) *)
(* (*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*         [ string_value Ad_loc_stack_Da ], *) *)
(* (*       process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *) *)
(* (*         [ *) *)
(* (*           process_generic_type Ad_constant_Da Ad_Pconst_string_Da *) *)
(* (*             [ string_value Ad_loc_Da, process_string_option ] *) *)
(* (*         ] *) *)
(* (*     ]. *) *)

(* (* Definition foo1 : ast_desc := *) *)
(* (*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *) *)
(* (*     [ *) *)
(* (*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *) *)
(* (*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*         [ string_value Ad_process_generic_type_Da ], *) *)
(* (*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *) *)
(* (*         [ *) *)
(* (*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *) *)
(* (*           none, *) *)
(* (*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_constraint_Da *) *)
(* (*             [ *) *)
(* (*               process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*                 [ string_value Ad_a_Da ], *) *)
(* (*               process_generic_type Ad_core_type_desc_Da *) *)
(* (*                 Ad_Ptyp_constr_Da *) *)
(* (*                 [ *) *)
(* (*                   ident *) *)
(* (*                     Ad_string_Da, *) *)
(* (*                   process_core_type_list *) *)
(* (*                     Ad_None *) *)
(* (*                 ] *) *)
(* (*             ], *) *)
(* (*           process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *) *)
(* (*             [ *) *)
(* (*               process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *) *)
(* (*               none, *) *)
(* (*               process_generic_type Ad_pattern_desc_Da *) *)
(* (*                 Ad_Ppat_constraint_Da *) *)
(* (*                 [ *) *)
(* (*                   process_generic_type *) *)
(* (*                     Ad_pattern_desc_Da *) *)
(* (*                     Ad_Ppat_var_Da *) *)
(* (*                     [ *) *)
(* (*                       string_value *) *)
(* (*                         Ad_b_Da *) *)
(* (*                     ], *) *)
(* (*                   process_generic_type *) *)
(* (*                     Ad_core_type_desc_Da *) *)
(* (*                     Ad_Ptyp_constr_Da *) *)
(* (*                     [ *) *)
(* (*                       ident *) *)
(* (*                         Ad_string_Da, *) *)
(* (*                       process_core_type_list *) *)
(* (*                         Ad_None *) *)
(* (*                     ] *) *)
(* (*                 ], *) *)
(* (*               process_generic_type Ad_expression_desc_Da *) *)
(* (*                 Ad_Pexp_fun_Da *) *)
(* (*                 [ *) *)
(* (*                   process_generic_type *) *)
(* (*                     Ad_arg_label_Da *) *)
(* (*                     Ad_Nolabel_Da *) *)
(* (*                     Ad_None, *) *)
(* (*                   none, *) *)
(* (*                   process_generic_type *) *)
(* (*                     Ad_pattern_desc_Da *) *)
(* (*                     Ad_Ppat_constraint_Da *) *)
(* (*                     [ *) *)
(* (*                       process_generic_type *) *)
(* (*                         Ad_pattern_desc_Da *) *)
(* (*                         Ad_Ppat_var_Da *) *)
(* (*                         [ *) *)
(* (*                           string_value *) *)
(* (*                             Ad_c_Da *) *)
(* (*                         ], *) *)
(* (*                       process_generic_type *) *)
(* (*                         Ad_core_type_desc_Da *) *)
(* (*                         Ad_Ptyp_constr_Da *) *)
(* (*                         [ *) *)
(* (*                           ident *) *)
(* (*                             Ad_list_Da, *) *)
(* (*                           process_core_type_list *) *)
(* (*                             [ *) *)
(* (*                               process_generic_type *) *)
(* (*                                 Ad_core_type_desc_Da *) *)
(* (*                                 Ad_Ptyp_constr_Da *) *)
(* (*                                 [ *) *)
(* (*                                   ident *) *)
(* (*                                     Ad_string_Da, *) *)
(* (*                                   process_core_type_list *) *)
(* (*                                     Ad_None *) *)
(* (*                                 ] *) *)
(* (*                             ] *) *)
(* (*                         ] *) *)
(* (*                     ], *) *)
(* (*                   process_generic_type *) *)
(* (*                     Ad_expression_desc_Da *) *)
(* (*                     Ad_Pexp_constraint_Da *) *)
(* (*                     [ *) *)
(* (*                       process_generic_type *) *)
(* (*                         Ad_expression_desc_Da *) *)
(* (*                         Ad_Pexp_constant_Da *) *)
(* (*                         [ *) *)
(* (*                           process_generic_type *) *)
(* (*                             Ad_constant_Da *) *)
(* (*                             Ad_Pconst_string_Da *) *)
(* (*                             [ *) *)
(* (*                               string_value *) *)
(* (*                                 Ad_process_generic_type_Da, *) *)
(* (*                               process_string_option *) *)
(* (*                             ] *) *)
(* (*                         ], *) *)
(* (*                       process_generic_type *) *)
(* (*                         Ad_core_type_desc_Da *) *)
(* (*                         Ad_Ptyp_constr_Da *) *)
(* (*                         [ *) *)
(* (*                           ident *) *)
(* (*                             Ad_string_Da, *) *)
(* (*                           process_core_type_list *) *)
(* (*                             Ad_None *) *)
(* (*                         ] *) *)
(* (*                     ] *) *)
(* (*                 ] *) *)
(* (*             ] *) *)
(* (*         ] *) *)
(* (*     ]. *) *)

(* (* Definition foo1 : ast_desc := *) *)
(* (*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *) *)
(* (*     [ *) *)
(* (*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *) *)
(* (*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*         [ string_value Ad_process_loc_Da ], *) *)
(* (*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *) *)
(* (*         [ *) *)
(* (*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *) *)
(* (*           none, *) *)
(* (*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*             [ string_value Ad_a_Da ], *) *)
(* (*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *) *)
(* (*             [ *) *)
(* (*               process_generic_type Ad_constant_Da *) *)
(* (*                 Ad_Pconst_string_Da *) *)
(* (*                 [ *) *)
(* (*                   string_value *) *)
(* (*                     Ad_process_loc_Da, *) *)
(* (*                   process_string_option *) *)
(* (*                 ] *) *)
(* (*             ] *) *)
(* (*         ] *) *)
(* (*     ]. *) *)

(* (* Definition foo1 : ast_desc := *) *)
(* (*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *) *)
(* (*     [ *) *)
(* (*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *) *)
(* (*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da [ string_value Ad_ident_Da ], *) *)
(* (*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *) *)
(* (*         [ *) *)
(* (*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *) *)
(* (*           none, *) *)
(* (*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*             [ string_value Ad_a_Da ], *) *)
(* (*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *) *)
(* (*             [ *) *)
(* (*               process_generic_type Ad_constant_Da *) *)
(* (*                 Ad_Pconst_string_Da *) *)
(* (*                 [ *) *)
(* (*                   string_value *) *)
(* (*                     Ad_ident_Da, *) *)
(* (*                   process_string_option *) *)
(* (*                 ] *) *)
(* (*             ] *) *)
(* (*         ] *) *)
(* (*     ]. *) *)

(* (* Definition foo1 : ast_desc := *) *)
(* (*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *) *)
(* (*     [ *) *)
(* (*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *) *)
(* (*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*         [ string_value Ad_process_string_loc_list_pattern_option_Da ], *) *)
(* (*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *) *)
(* (*         [ *) *)
(* (*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *) *)
(* (*           none, *) *)
(* (*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*             [ string_value Ad_x_Da ], *) *)
(* (*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *) *)
(* (*             [ *) *)
(* (*               process_generic_type Ad_constant_Da *) *)
(* (*                 Ad_Pconst_string_Da *) *)
(* (*                 [ *) *)
(* (*                   string_value *) *)
(* (*                     Ad_process_string_loc_list_pattern_option_Da, *) *)
(* (*                   process_string_option *) *)
(* (*                 ] *) *)
(* (*             ] *) *)
(* (*         ] *) *)
(* (*     ]. *) *)

(* (* Definition foo1 : ast_desc := *) *)
(* (*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *) *)
(* (*     [ *) *)
(* (*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *) *)
(* (*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*         [ string_value Ad_process_arg_label_expression_Da ], *) *)
(* (*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *) *)
(* (*         [ *) *)
(* (*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *) *)
(* (*           none, *) *)
(* (*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*             [ string_value Ad_x_Da ], *) *)
(* (*           process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *) *)
(* (*             [ *) *)
(* (*               process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *) *)
(* (*               none, *) *)
(* (*               process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*                 [ string_value Ad_y_Da ], *) *)
(* (*               process_generic_type Ad_expression_desc_Da *) *)
(* (*                 Ad_Pexp_constant_Da *) *)
(* (*                 [ *) *)
(* (*                   process_generic_type *) *)
(* (*                     Ad_constant_Da *) *)
(* (*                     Ad_Pconst_string_Da *) *)
(* (*                     [ *) *)
(* (*                       string_value *) *)
(* (*                         Ad_process_arg_label_expression_Da, *) *)
(* (*                       process_string_option *) *)
(* (*                     ] *) *)
(* (*                 ] *) *)
(* (*             ] *) *)
(* (*         ] *) *)
(* (*     ]. *) *)

(* (* Definition foo1 : ast_desc := *) *)
(* (*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *) *)
(* (*     [ *) *)
(* (*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *) *)
(* (*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*         [ string_value Ad_process_expression_list_Da ], *) *)
(* (*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *) *)
(* (*         [ *) *)
(* (*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *) *)
(* (*           none, *) *)
(* (*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*             [ string_value Ad_x_Da ], *) *)
(* (*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *) *)
(* (*             [ *) *)
(* (*               process_generic_type Ad_constant_Da *) *)
(* (*                 Ad_Pconst_string_Da *) *)
(* (*                 [ *) *)
(* (*                   string_value *) *)
(* (*                     Ad_process_expression_list_Da, *) *)
(* (*                   process_string_option *) *)
(* (*                 ] *) *)
(* (*             ] *) *)
(* (*         ] *) *)
(* (*     ]. *) *)

(* (* Definition foo1 : ast_desc := *) *)
(* (*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *) *)
(* (*     [ *) *)
(* (*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *) *)
(* (*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*         [ string_value Ad_process_structure_items_Da ], *) *)
(* (*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *) *)
(* (*         [ *) *)
(* (*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *) *)
(* (*           none, *) *)
(* (*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *) *)
(* (*             [ string_value Ad_x_Da ], *) *)
(* (*           process_generic_type Ad_expression_desc_Da Ad_Pexp_apply_Da *) *)
(* (*             [ *) *)
(* (*               process_generic_type Ad_expression_desc_Da *) *)
(* (*                 Ad_Pexp_ident_Da *) *)
(* (*                 [ ident Ad_caret ], *) *)
(* (*               process_arg_label_expression_list *) *)
(* (*                 [ *) *)
(* (*                   process_arg_label_expression *) *)
(* (*                     (process_generic_type *) *)
(* (*                       Ad_arg_label_Da *) *)
(* (*                       Ad_Nolabel_Da *) *)
(* (*                       Ad_None) *) *)
(* (*                     (process_generic_type *) *)
(* (*                       Ad_expression_desc_Da *) *)
(* (*                       Ad_Pexp_constant_Da *) *)
(* (*                       [ *) *)
(* (*                         process_generic_type *) *)
(* (*                           Ad_constant_Da *) *)
(* (*                           Ad_Pconst_string_Da *) *)
(* (*                           [ *) *)
(* (*                             string_value *) *)
(* (*                               Ad_process_structure_items_Da, *) *)
(* (*                             process_string_option *) *)
(* (*                           ] *) *)
(* (*                       ]), *) *)
(* (*                   process_arg_label_expression *) *)
(* (*                     (process_generic_type *) *)
(* (*                       Ad_arg_label_Da *) *)
(* (*                       Ad_Nolabel_Da *) *)
(* (*                       Ad_None) *) *)
(* (*                     (process_generic_type *) *)
(* (*                       Ad_expression_desc_Da *) *)
(* (*                       Ad_Pexp_ident_Da *) *)
(* (*                       [ *) *)
(* (*                         ident *) *)
(* (*                           Ad_x_Da *) *)
(* (*                       ]) *) *)
(* (*                 ] *) *)
(* (*             ] *) *)
(* (*         ] *) *)
(* (*     ]. *) *)

(* (* Definition foo1 : ast_desc := *) *)
(* (*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *) *)
(* (*     [ *) *)
(* (*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *) *)
(* (*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da [ string_value Ad_foo1_Da ], *) *)
(* (*       process_generic_type Ad_expression_desc_Da Ad_Pexp_apply_Da *) *)
(* (*         [ *) *)
(* (*           process_generic_type Ad_expression_desc_Da Ad_Pexp_ident_Da *) *)
(* (*             [ ident Ad_process_generic_type_Da ], *) *)
(* (*           process_arg_label_expression_list *) *)
(* (*             [ *) *)
(* (*               process_arg_label_expression *) *)
(* (*                 (process_generic_type *) *)
(* (*                   Ad_arg_label_Da *) *)
(* (*                   Ad_Nolabel_Da *) *)
(* (*                   Ad_None) *) *)
(* (*                 (process_generic_type *) *)
(* (*                   Ad_expression_desc_Da *) *)
(* (*                   Ad_Pexp_constant_Da *) *)
(* (*                   [ *) *)
(* (*                     process_generic_type *) *)
(* (*                       Ad_constant_Da *) *)
(* (*                       Ad_Pconst_string_Da *) *)
(* (*                       [ *) *)
(* (*                         string_value *) *)
(* (*                           Ad_structure_item_desc_Da, *) *)
(* (*                         process_string_option *) *)
(* (*                       ] *) *)
(* (*                   ]), *) *)
(* (*               process_arg_label_expression *) *)
(* (*                 (process_generic_type *) *)
(* (*                   Ad_arg_label_Da *) *)
(* (*                   Ad_Nolabel_Da *) *)
(* (*                   Ad_None) *) *)
(* (*                 (process_generic_type *) *)
(* (*                   Ad_expression_desc_Da *) *)
(* (*                   Ad_Pexp_constant_Da *) *)
(* (*                   [ *) *)
(* (*                     process_generic_type *) *)
(* (*                       Ad_constant_Da *) *)
(* (*                       Ad_Pconst_string_Da *) *)
(* (*                       [ *) *)
(* (*                         string_value *) *)
(* (*                           Ad_Pstr_type_Da, *) *)
(* (*                         process_string_option *) *)
(* (*                       ] *) *)
(* (*                   ]), *) *)
(* (*               process_arg_label_expression *) *)
(* (*                 (process_generic_type *) *)
(* (*                   Ad_arg_label_Da *) *)
(* (*                   Ad_Nolabel_Da *) *)
(* (*                   Ad_None) *) *)
(* (*                 (process_generic_type *) *)
(* (*                   Ad_expression_desc_Da *) *)
(* (*                   Ad_Pexp_construct_Da *) *)
(* (*                   [ *) *)
(* (*                     ident *) *)
(* (*                       Ad_::_Da, *) *)
(* (*                     process_generic_type *) *)
(* (*                       Ad_expression_desc_Da *) *)
(* (*                       Ad_Pexp_tuple_Da *) *)
(* (*                       [ *) *)
(* (*                         process_expression_list *) *)
(* (*                           [ *) *)
(* (*                             process_generic_type *) *)
(* (*                               Ad_expression_desc_Da *) *)
(* (*                               Ad_Pexp_apply_Da *) *)
(* (*                               [ *) *)
(* (*                                 process_generic_type *) *)
(* (*                                   Ad_expression_desc_Da *) *)
(* (*                                   Ad_Pexp_ident_Da *) *)
(* (*                                   [ *) *)
(* (*                                     ident *) *)
(* (*                                       Ad_process_generic_type_Da *) *)
(* (*                                   ], *) *)
(* (*                                 process_arg_label_expression_list *) *)
(* (*                                   [ *) *)
(* (*                                     process_arg_label_expression *) *)
(* (*                                       (process_generic_type *) *)
(* (*                                         Ad_arg_label_Da *) *)
(* (*                                         Ad_Nolabel_Da *) *)
(* (*                                         Ad_None) *) *)
(* (*                                       (process_generic_type *) *)
(* (*                                         Ad_expression_desc_Da *) *)
(* (*                                         Ad_Pexp_constant_Da *) *)
(* (*                                         [ *) *)
(* (*                                           process_generic_type *) *)
(* (*                                             Ad_constant_Da *) *)
(* (*                                             Ad_Pconst_string_Da *) *)
(* (*                                             [ *) *)
(* (*                                               string_value *) *)
(* (*                                                 Ad_rec_flag_Da, *) *)
(* (*                                               process_string_option *) *)
(* (*                                             ] *) *)
(* (*                                         ]), *) *)
(* (*                                     process_arg_label_expression *) *)
(* (*                                       (process_generic_type *) *)
(* (*                                         Ad_arg_label_Da *) *)
(* (*                                         Ad_Nolabel_Da *) *)
(* (*                                         Ad_None) *) *)
(* (*                                       (process_generic_type *) *)
(* (*                                         Ad_expression_desc_Da *) *)
(* (*                                         Ad_Pexp_constant_Da *) *)
(* (*                                         [ *) *)
(* (*                                           process_generic_type *) *)
(* (*                                             Ad_constant_Da *) *)
(* (*                                             Ad_Pconst_string_Da *) *)
(* (*                                             [ *) *)
(* (*                                               string_value *) *)
(* (*                                                 Ad_Recursive_Da, *) *)
(* (*                                               process_string_option *) *)
(* (*                                             ] *) *)
(* (*                                         ]), *) *)
(* (*                                     process_arg_label_expression *) *)
(* (*                                       (process_generic_type *) *)
(* (*                                         Ad_arg_label_Da *) *)
(* (*                                         Ad_Nolabel_Da *) *)
(* (*                                         Ad_None) *) *)
(* (*                                       (process_generic_type *) *)
(* (*                                         Ad_expression_desc_Da *) *)
(* (*                                         Ad_Pexp_construct_Da *) *)
(* (*                                         [ *) *)
(* (*                                           ident *) *)
(* (*                                             Ad_empty_list, *) *)
(* (*                                           none *) *)
(* (*                                         ]) *) *)
(* (*                                   ] *) *)
(* (*                               ], *) *)
(* (*                             process_generic_type *) *)
(* (*                               Ad_expression_desc_Da *) *)
(* (*                               Ad_Pexp_construct_Da *) *)
(* (*                               [ *) *)
(* (*                                 ident *) *)
(* (*                                   Ad_::_Da, *) *)
(* (*                                 process_generic_type *) *)
(* (*                                   Ad_expression_desc_Da *) *)
(* (*                                   Ad_Pexp_tuple_Da *) *)
(* (*                                   [ *) *)
(* (*                                     process_expression_list *) *)
(* (*                                       [ *) *)
(* (*                                         process_generic_type *) *)
(* (*                                           Ad_expression_desc_Da *) *)
(* (*                                           Ad_Pexp_apply_Da *) *)
(* (*                                           [ *) *)
(* (*                                             process_generic_type *) *)
(* (*                                               Ad_expression_desc_Da *) *)
(* (*                                               Ad_Pexp_ident_Da *) *)
(* (*                                               [ *) *)
(* (*                                                 ident *) *)
(* (*                                                   Ad_process_type_declaration_list_Da *) *)
(* (*                                               ], *) *)
(* (*                                             process_arg_label_expression_list *) *)
(* (*                                               [ *) *)
(* (*                                                 process_arg_label_expression *) *)
(* (*                                                   (process_generic_type *) *)
(* (*                                                     Ad_arg_label_Da *) *)
(* (*                                                     Ad_Nolabel_Da *) *)
(* (*                                                     Ad_None) *) *)
(* (*                                                   (process_generic_type *) *)
(* (*                                                     Ad_expression_desc_Da *) *)
(* (*                                                     Ad_Pexp_construct_Da *) *)
(* (*                                                     [ *) *)
(* (*                                                       ident *) *)
(* (*                                                         Ad_::_Da, *) *)
(* (*                                                       process_generic_type *) *)
(* (*                                                         Ad_expression_desc_Da *) *)
(* (*                                                         Ad_Pexp_tuple_Da *) *)
(* (*                                                         [ *) *)
(* (*                                                           process_expression_list *) *)
(* (*                                                             [ *) *)
(* (*                                                               process_generic_type *) *)
(* (*                                                                 Ad_expression_desc_Da *) *)
(* (*                                                                 Ad_Pexp_apply_Da *) *)
(* (*                                                                 [ *) *)
(* (*                                                                   process_generic_type *) *)
(* (*                                                                     Ad_expression_desc_Da *) *)
(* (*                                                                     Ad_Pexp_ident_Da *) *)
(* (*                                                                     [ *) *)
(* (*                                                                       ident *) *)
(* (*                                                                         Ad_caret *) *)
(* (*                                                                     ], *) *)
(* (*                                                                   process_arg_label_expression_list *) *)
(* (*                                                                     [ *) *)
(* (*                                                                       process_arg_label_expression *) *)
(* (*                                                                         (process_generic_type *) *)
(* (*                                                                           Ad_arg_label_Da *) *)
(* (*                                                                           Ad_Nolabel_Da *) *)
(* (*                                                                           Ad_None) *) *)
(* (*                                                                         (process_generic_type *) *)
(* (*                                                                           Ad_expression_desc_Da *) *)
(* (*                                                                           Ad_Pexp_apply_Da *) *)
(* (*                                                                           [ *) *)
(* (*                                                                             process_generic_type *) *)
(* (*                                                                               Ad_expression_desc_Da *) *)
(* (*                                                                               Ad_Pexp_ident_Da *) *)
(* (*                                                                               [ *) *)
(* (*                                                                                 ident *) *)
(* (*                                                                                   Ad_string_Da *) *)
(* (*                                                                               ], *) *)
(* (*                                                                             process_arg_label_expression_list *) *)
(* (*                                                                               [ *) *)
(* (*                                                                                 process_arg_label_expression *) *)
(* (*                                                                                   (process_generic_type *) *)
(* (*                                                                                     Ad_arg_label_Da *) *)
(* (*                                                                                     Ad_Nolabel_Da *) *)
(* (*                                                                                     Ad_None) *) *)
(* (*                                                                                   (process_generic_type *) *)
(* (*                                                                                     Ad_expression_desc_Da *) *)
(* (*                                                                                     Ad_Pexp_constant_Da *) *)
(* (*                                                                                     [ *) *)
(* (*                                                                                       process_generic_type *) *)
(* (*                                                                                         Ad_constant_Da *) *)
(* (*                                                                                         Ad_Pconst_string_Da *) *)
(* (*                                                                                         [ *) *)
(* (*                                                                                           string_value *) *)
(* (*                                                                                             Ad_Da, *) *)
(* (*                                                                                           process_string_option *) *)
(* (*                                                                                         ] *) *)
(* (*                                                                                     ]) *) *)
(* (*                                                                               ] *) *)
(* (*                                                                           ]), *) *)
(* (*                                                                       process_arg_label_expression *) *)
(* (*                                                                         (process_generic_type *) *)
(* (*                                                                           Ad_arg_label_Da *) *)
(* (*                                                                           Ad_Nolabel_Da *) *)
(* (*                                                                           Ad_None) *) *)
(* (*                                                                         (process_generic_type *) *)
(* (*                                                                           Ad_expression_desc_Da *) *)
(* (*                                                                           Ad_Pexp_apply_Da *) *)
(* (*                                                                           [ *) *)
(* (*                                                                             process_generic_type *) *)
(* (*                                                                               Ad_expression_desc_Da *) *)
(* (*                                                                               Ad_Pexp_ident_Da *) *)
(* (*                                                                               [ *) *)
(* (*                                                                                 ident *) *)
(* (*                                                                                   Ad_caret *) *)
(* (*                                                                               ], *) *)
(* (*                                                                             process_arg_label_expression_list *) *)
(* (*                                                                               [ *) *)
(* (*                                                                                 process_arg_label_expression *) *)
(* (*                                                                                   (process_generic_type *) *)
(* (*                                                                                     Ad_arg_label_Da *) *)
(* (*                                                                                     Ad_Nolabel_Da *) *)
(* (*                                                                                     Ad_None) *) *)
(* (*                                                                                   (process_generic_type *) *)
(* (*                                                                                     Ad_expression_desc_Da *) *)
(* (*                                                                                     Ad_Pexp_apply_Da *) *)
(* (*                                                                                     [ *) *)
(* (*                                                                                       process_generic_type *) *)
(* (*                                                                                         Ad_expression_desc_Da *) *)
(* (*                                                                                         Ad_Pexp_ident_Da *) *)
(* (*                                                                                         [ *) *)
(* (*                                                                                           ident *) *)
(* (*                                                                                             Ad_process_params_Da *) *)
(* (*                                                                                         ], *) *)
(* (*                                                                                       process_arg_label_expression_list *) *)
(* (*                                                                                         [ *) *)
(* (*                                                                                           process_arg_label_expression *) *)
(* (*                                                                                             (process_generic_type *) *)
(* (*                                                                                               Ad_arg_label_Da *) *)
(* (*                                                                                               Ad_Nolabel_Da *) *)
(* (*                                                                                               Ad_None) *) *)
(* (*                                                                                             (process_generic_type *) *)
(* (*                                                                                               Ad_expression_desc_Da *) *)
(* (*                                                                                               Ad_Pexp_construct_Da *) *)
(* (*                                                                                               [ *) *)
(* (*                                                                                                 ident *) *)
(* (*                                                                                                   Ad_empty_list, *) *)
(* (*                                                                                                 none *) *)
(* (*                                                                                               ]) *) *)
(* (*                                                                                         ] *) *)
(* (*                                                                                     ]), *) *)
(* (*                                                                                 process_arg_label_expression *) *)
(* (*                                                                                   (process_generic_type *) *)
(* (*                                                                                     Ad_arg_label_Da *) *)
(* (*                                                                                     Ad_Nolabel_Da *) *)
(* (*                                                                                     Ad_None) *) *)
(* (*                                                                                   (process_generic_type *) *)
(* (*                                                                                     Ad_expression_desc_Da *) *)
(* (*                                                                                     Ad_Pexp_apply_Da *) *)
(* (*                                                                                     [ *) *)
(* (*                                                                                       process_generic_type *) *)
(* (*                                                                                         Ad_expression_desc_Da *) *)
(* (*                                                                                         Ad_Pexp_ident_Da *) *)
(* (*                                                                                         [ *) *)
(* (*                                                                                           ident *) *)
(* (*                                                                                             Ad_caret *) *)
(* (*                                                                                         ], *) *)
(* (*                                                                                       process_arg_label_expression_list *) *)
(* (*                                                                                         [ *) *)
(* (*                                                                                           process_arg_label_expression *) *)
(* (*                                                                                             (process_generic_type *) *)
(* (*                                                                                               Ad_arg_label_Da *) *)
(* (*                                                                                               Ad_Nolabel_Da *) *)
(* (*                                                                                               Ad_None) *) *)
(* (*                                                                                             (process_generic_type *) *)
(* (*                                                                                               Ad_expression_desc_Da *) *)
(* (*                                                                                               Ad_Pexp_apply_Da *) *)
(* (*                                                                                               [ *) *)
(* (*                                                                                                 process_generic_type *) *)
(* (*                                                                                                   Ad_expression_desc_Da *) *)
(* (*                                                                                                   Ad_Pexp_ident_Da *) *)
(* (*                                                                                                   [ *) *)
(* (*                                                                                                     ident *) *)
(* (*                                                                                                       Ad_process_cstrs_Da *) *)
(* (*                                                                                                   ], *) *)
(* (*                                                                                                 process_arg_label_expression_list *) *)
(* (*                                                                                                   [ *) *)
(* (*                                                                                                     process_arg_label_expression *) *)
(* (*                                                                                                       (process_generic_type *) *)
(* (*                                                                                                         Ad_arg_label_Da *) *)
(* (*                                                                                                         Ad_Nolabel_Da *) *)
(* (*                                                                                                         Ad_None) *) *)
(* (*                                                                                                       (process_generic_type *) *)
(* (*                                                                                                         Ad_expression_desc_Da *) *)
(* (*                                                                                                         Ad_Pexp_construct_Da *) *)
(* (*                                                                                                         [ *) *)
(* (*                                                                                                           ident *) *)
(* (*                                                                                                             Ad_empty_list, *) *)
(* (*                                                                                                           none *) *)
(* (*                                                                                                         ]) *) *)
(* (*                                                                                                   ] *) *)
(* (*                                                                                               ]), *) *)
(* (*                                                                                           process_arg_label_expression *) *)
(* (*                                                                                             (process_generic_type *) *)
(* (*                                                                                               Ad_arg_label_Da *) *)
(* (*                                                                                               Ad_Nolabel_Da *) *)
(* (*                                                                                               Ad_None) *) *)
(* (*                                                                                             (process_generic_type *) *)
(* (*                                                                                               Ad_expression_desc_Da *) *)
(* (*                                                                                               Ad_Pexp_apply_Da *) *)
(* (*                                                                                               [ *) *)
(* (*                                                                                                 process_generic_type *) *)
(* (*                                                                                                   Ad_expression_desc_Da *) *)
(* (*                                                                                                   Ad_Pexp_ident_Da *) *)
(* (*                                                                                                   [ *) *)
(* (*                                                                                                     ident *) *)
(* (*                                                                                                       Ad_caret *) *)
(* (*                                                                                                   ], *) *)
(* (*                                                                                                 process_arg_label_expression_list *) *)
(* (*                                                                                                   [ *) *)
(* (*                                                                                                     process_arg_label_expression *) *)
(* (*                                                                                                       (process_generic_type *) *)
(* (*                                                                                                         Ad_arg_label_Da *) *)
(* (*                                                                                                         Ad_Nolabel_Da *) *)
(* (*                                                                                                         Ad_None) *) *)
(* (*                                                                                                       (process_generic_type *) *)
(* (*                                                                                                         Ad_expression_desc_Da *) *)
(* (*                                                                                                         Ad_Pexp_apply_Da *) *)
(* (*                                                                                                         [ *) *)
(* (*                                                                                                           process_generic_type *) *)
(* (*                                                                                                             Ad_expression_desc_Da *) *)
(* (*                                                                                                             Ad_Pexp_ident_Da *) *)
(* (*                                                                                                             [ *) *)
(* (*                                                                                                               ident *) *)
(* (*                                                                                                                 Ad_process_generic_type_Da *) *)
(* (*                                                                                                             ], *) *)
(* (*                                                                                                           process_arg_label_expression_list *) *)
(* (*                                                                                                             [ *) *)
(* (*                                                                                                               process_arg_label_expression *) *)
(* (*                                                                                                                 (process_generic_type *) *)
(* (*                                                                                                                   Ad_arg_label_Da *) *)
(* (*                                                                                                                   Ad_Nolabel_Da *) *)
(* (*                                                                                                                   Ad_None) *) *)
(* (*                                                                                                                 (process_generic_type *) *)
(* (*                                                                                                                   Ad_expression_desc_Da *) *)
(* (*                                                                                                                   Ad_Pexp_constant_Da *) *)
(* (*                                                                                                                   [ *) *)
(* (*                                                                                                                     process_generic_type *) *)
(* (*                                                                                                                       Ad_constant_Da *) *)
(* (*                                                                                                                       Ad_Pconst_string_Da *) *)
(* (*                                                                                                                       [ *) *)
(* (*                                                                                                                         string_value *) *)
(* (*                                                                                                                           Ad_type_kind_Da, *) *)
(* (*                                                                                                                         process_string_option *) *)
(* (*                                                                                                                       ] *) *)
(* (*                                                                                                                   ]), *) *)
(* (*                                                                                                               process_arg_label_expression *) *)
(* (*                                                                                                                 (process_generic_type *) *)
(* (*                                                                                                                   Ad_arg_label_Da *) *)
(* (*                                                                                                                   Ad_Nolabel_Da *) *)
(* (*                                                                                                                   Ad_None) *) *)
(* (*                                                                                                                 (process_generic_type *) *)
(* (*                                                                                                                   Ad_expression_desc_Da *) *)
(* (*                                                                                                                   Ad_Pexp_constant_Da *) *)
(* (*                                                                                                                   [ *) *)
(* (*                                                                                                                     process_generic_type *) *)
(* (*                                                                                                                       Ad_constant_Da *) *)
(* (*                                                                                                                       Ad_Pconst_string_Da *) *)
(* (*                                                                                                                       [ *) *)
(* (*                                                                                                                         string_value *) *)
(* (*                                                                                                                           Ad_Ptype_abstract_Da, *) *)
(* (*                                                                                                                         process_string_option *) *)
(* (*                                                                                                                       ] *) *)
(* (*                                                                                                                   ]), *) *)
(* (*                                                                                                               process_arg_label_expression *) *)
(* (*                                                                                                                 (process_generic_type *) *)
(* (*                                                                                                                   Ad_arg_label_Da *) *)
(* (*                                                                                                                   Ad_Nolabel_Da *) *)
(* (*                                                                                                                   Ad_None) *) *)
(* (*                                                                                                                 (process_generic_type *) *)
(* (*                                                                                                                   Ad_expression_desc_Da *) *)
(* (*                                                                                                                   Ad_Pexp_construct_Da *) *)
(* (*                                                                                                                   [ *) *)
(* (*                                                                                                                     ident *) *)
(* (*                                                                                                                       Ad_empty_list, *) *)
(* (*                                                                                                                     none *) *)
(* (*                                                                                                                   ]) *) *)
(* (*                                                                                                             ] *) *)
(* (*                                                                                                         ]), *) *)
(* (*                                                                                                     process_arg_label_expression *) *)
(* (*                                                                                                       (process_generic_type *) *)
(* (*                                                                                                         Ad_arg_label_Da *) *)
(* (*                                                                                                         Ad_Nolabel_Da *) *)
(* (*                                                                                                         Ad_None) *) *)
(* (*                                                                                                       (process_generic_type *) *)
(* (*                                                                                                         Ad_expression_desc_Da *) *)
(* (*                                                                                                         Ad_Pexp_apply_Da *) *)
(* (*                                                                                                         [ *) *)
(* (*                                                                                                           process_generic_type *) *)
(* (*                                                                                                             Ad_expression_desc_Da *) *)
(* (*                                                                                                             Ad_Pexp_ident_Da *) *)
(* (*                                                                                                             [ *) *)
(* (*                                                                                                               ident *) *)
(* (*                                                                                                                 Ad_caret *) *)
(* (*                                                                                                             ], *) *)
(* (*                                                                                                           process_arg_label_expression_list *) *)
(* (*                                                                                                             [ *) *)
(* (*                                                                                                               process_arg_label_expression *) *)
(* (*                                                                                                                 (process_generic_type *) *)
(* (*                                                                                                                   Ad_arg_label_Da *) *)
(* (*                                                                                                                   Ad_Nolabel_Da *) *)
(* (*                                                                                                                   Ad_None) *) *)
(* (*                                                                                                                 (process_generic_type *) *)
(* (*                                                                                                                   Ad_expression_desc_Da *) *)
(* (*                                                                                                                   Ad_Pexp_apply_Da *) *)
(* (*                                                                                                                   [ *) *)
(* (*                                                                                                                     process_generic_type *) *)
(* (*                                                                                                                       Ad_expression_desc_Da *) *)
(* (*                                                                                                                       Ad_Pexp_ident_Da *) *)
(* (*                                                                                                                       [ *) *)
(* (*                                                                                                                         ident *) *)
(* (*                                                                                                                           Ad_process_generic_type_Da *) *)
(* (*                                                                                                                       ], *) *)
(* (*                                                                                                                     process_arg_label_expression_list *) *)
(* (*                                                                                                                       [ *) *)
(* (*                                                                                                                         process_arg_label_expression *) *)
(* (*                                                                                                                           (process_generic_type *) *)
(* (*                                                                                                                             Ad_arg_label_Da *) *)
(* (*                                                                                                                             Ad_Nolabel_Da *) *)
(* (*                                                                                                                             Ad_None) *) *)
(* (*                                                                                                                           (process_generic_type *) *)
(* (*                                                                                                                             Ad_expression_desc_Da *) *)
(* (*                                                                                                                             Ad_Pexp_constant_Da *) *)
(* (*                                                                                                                             [ *) *)
(* (*                                                                                                                               process_generic_type *) *)
(* (*                                                                                                                                 Ad_constant_Da *) *)
(* (*                                                                                                                                 Ad_Pconst_string_Da *) *)
(* (*                                                                                                                                 [ *) *)
(* (*                                                                                                                                   string_value *) *)
(* (*                                                                                                                                     Ad_private_flag_Da, *) *)
(* (*                                                                                                                                   process_string_option *) *)
(* (*                                                                                                                                 ] *) *)
(* (*                                                                                                                             ]), *) *)
(* (*                                                                                                                         process_arg_label_expression *) *)
(* (*                                                                                                                           (process_generic_type *) *)
(* (*                                                                                                                             Ad_arg_label_Da *) *)
(* (*                                                                                                                             Ad_Nolabel_Da *) *)
(* (*                                                                                                                             Ad_None) *) *)
(* (*                                                                                                                           (process_generic_type *) *)
(* (*                                                                                                                             Ad_expression_desc_Da *) *)
(* (*                                                                                                                             Ad_Pexp_constant_Da *) *)
(* (*                                                                                                                             [ *) *)
(* (*                                                                                                                               process_generic_type *) *)
(* (*                                                                                                                                 Ad_constant_Da *) *)
(* (*                                                                                                                                 Ad_Pconst_string_Da *) *)
(* (*                                                                                                                                 [ *) *)
(* (*                                                                                                                                   string_value *) *)
(* (*                                                                                                                                     Ad_Public_Da, *) *)
(* (*                                                                                                                                   process_string_option *) *)
(* (*                                                                                                                                 ] *) *)
(* (*                                                                                                                             ]), *) *)
(* (*                                                                                                                         process_arg_label_expression *) *)
(* (*                                                                                                                           (process_generic_type *) *)
(* (*                                                                                                                             Ad_arg_label_Da *) *)
(* (*                                                                                                                             Ad_Nolabel_Da *) *)
(* (*                                                                                                                             Ad_None) *) *)
(* (*                                                                                                                           (process_generic_type *) *)
(* (*                                                                                                                             Ad_expression_desc_Da *) *)
(* (*                                                                                                                             Ad_Pexp_construct_Da *) *)
(* (*                                                                                                                             [ *) *)
(* (*                                                                                                                               ident *) *)
(* (*                                                                                                                                 Ad_empty_list, *) *)
(* (*                                                                                                                               none *) *)
(* (*                                                                                                                             ]) *) *)
(* (*                                                                                                                       ] *) *)
(* (*                                                                                                                   ]), *) *)
(* (*                                                                                                               process_arg_label_expression *) *)
(* (*                                                                                                                 (process_generic_type *) *)
(* (*                                                                                                                   Ad_arg_label_Da *) *)
(* (*                                                                                                                   Ad_Nolabel_Da *) *)
(* (*                                                                                                                   Ad_None) *) *)
(* (*                                                                                                                 (process_generic_type *) *)
(* (*                                                                                                                   Ad_expression_desc_Da *) *)
(* (*                                                                                                                   Ad_Pexp_apply_Da *) *)
(* (*                                                                                                                   [ *) *)
(* (*                                                                                                                     process_generic_type *) *)
(* (*                                                                                                                       Ad_expression_desc_Da *) *)
(* (*                                                                                                                       Ad_Pexp_ident_Da *) *)
(* (*                                                                                                                       [ *) *)
(* (*                                                                                                                         ident *) *)
(* (*                                                                                                                           Ad_process_generic_type_Da *) *)
(* (*                                                                                                                       ], *) *)
(* (*                                                                                                                     process_arg_label_expression_list *) *)
(* (*                                                                                                                       [ *) *)
(* (*                                                                                                                         process_arg_label_expression *) *)
(* (*                                                                                                                           (process_generic_type *) *)
(* (*                                                                                                                             Ad_arg_label_Da *) *)
(* (*                                                                                                                             Ad_Nolabel_Da *) *)
(* (*                                                                                                                             Ad_None) *) *)
(* (*                                                                                                                           (process_generic_type *) *)
(* (*                                                                                                                             Ad_expression_desc_Da *) *)
(* (*                                                                                                                             Ad_Pexp_constant_Da *) *)
(* (*                                                                                                                             [ *) *)
(* (*                                                                                                                               process_generic_type *) *)
(* (*                                                                                                                                 Ad_constant_Da *) *)
(* (*                                                                                                                                 Ad_Pconst_string_Da *) *)
(* (*                                                                                                                                 [ *) *)
(* (*                                                                                                                                   string_value *) *)
(* (*                                                                                                                                     Ad_core_type_desc_Da, *) *)
(* (*                                                                                                                                   process_string_option *) *)
(* (*                                                                                                                                 ] *) *)
(* (*                                                                                                                             ]), *) *)
(* (*                                                                                                                         process_arg_label_expression *) *)
(* (*                                                                                                                           (process_generic_type *) *)
(* (*                                                                                                                             Ad_arg_label_Da *) *)
(* (*                                                                                                                             Ad_Nolabel_Da *) *)
(* (*                                                                                                                             Ad_None) *) *)
(* (*                                                                                                                           (process_generic_type *) *)
(* (*                                                                                                                             Ad_expression_desc_Da *) *)
(* (*                                                                                                                             Ad_Pexp_constant_Da *) *)
(* (*                                                                                                                             [ *) *)
(* (*                                                                                                                               process_generic_type *) *)
(* (*                                                                                                                                 Ad_constant_Da *) *)
(* (*                                                                                                                                 Ad_Pconst_string_Da *) *)
(* (*                                                                                                                                 [ *) *)
(* (*                                                                                                                                   string_value *) *)
(* (*                                                                                                                                     Ad_Ptyp_constr_Da, *) *)
(* (*                                                                                                                                   process_string_option *) *)
(* (*                                                                                                                                 ] *) *)
(* (*                                                                                                                             ]), *) *)
(* (*                                                                                                                         process_arg_label_expression *) *)
(* (*                                                                                                                           (process_generic_type *) *)
(* (*                                                                                                                             Ad_arg_label_Da *) *)
(* (*                                                                                                                             Ad_Nolabel_Da *) *)
(* (*                                                                                                                             Ad_None) *) *)
(* (*                                                                                                                           (process_generic_type *) *)
(* (*                                                                                                                             Ad_expression_desc_Da *) *)
(* (*                                                                                                                             Ad_Pexp_construct_Da *) *)
(* (*                                                                                                                             [ *) *)
(* (*                                                                                                                               ident *) *)
(* (*                                                                                                                                 Ad_::_Da, *) *)
(* (*                                                                                                                               process_generic_type *) *)
(* (*                                                                                                                                 Ad_expression_desc_Da *) *)
(* (*                                                                                                                                 Ad_Pexp_tuple_Da *) *)
(* (*                                                                                                                                 [ *) *)
(* (*                                                                                                                                   process_expression_list *) *)
(* (*                                                                                                                                     [ *) *)
(* (*                                                                                                                                       process_generic_type *) *)
(* (*                                                                                                                                         Ad_expression_desc_Da *) *)
(* (*                                                                                                                                         Ad_Pexp_apply_Da *) *)
(* (*                                                                                                                                         [ *) *)
(* (*                                                                                                                                           process_generic_type *) *)
(* (*                                                                                                                                             Ad_expression_desc_Da *) *)
(* (*                                                                                                                                             Ad_Pexp_ident_Da *) *)
(* (*                                                                                                                                             [ *) *)
(* (*                                                                                                                                               ident *) *)
(* (*                                                                                                                                                 Ad_ident_Da *) *)
(* (*                                                                                                                                             ], *) *)
(* (*                                                                                                                                           process_arg_label_expression_list *) *)
(* (*                                                                                                                                             [ *) *)
(* (*                                                                                                                                               process_arg_label_expression *) *)
(* (*                                                                                                                                                 (process_generic_type *) *)
(* (*                                                                                                                                                   Ad_arg_label_Da *) *)
(* (*                                                                                                                                                   Ad_Nolabel_Da *) *)
(* (*                                                                                                                                                   Ad_None) *) *)
(* (*                                                                                                                                                 (process_generic_type *) *)
(* (*                                                                                                                                                   Ad_expression_desc_Da *) *)
(* (*                                                                                                                                                   Ad_Pexp_constant_Da *) *)
(* (*                                                                                                                                                   [ *) *)
(* (*                                                                                                                                                     process_generic_type *) *)
(* (*                                                                                                                                                       Ad_constant_Da *) *)
(* (*                                                                                                                                                       Ad_Pconst_string_Da *) *)
(* (*                                                                                                                                                       [ *) *)
(* (*                                                                                                                                                         string_value *) *)
(* (*                                                                                                                                                           Ad_Obj.t_Da, *) *)
(* (*                                                                                                                                                         process_string_option *) *)
(* (*                                                                                                                                                       ] *) *)
(* (*                                                                                                                                                   ]) *) *)
(* (*                                                                                                                                             ] *) *)
(* (*                                                                                                                                         ], *) *)
(* (*                                                                                                                                       process_generic_type *) *)
(* (*                                                                                                                                         Ad_expression_desc_Da *) *)
(* (*                                                                                                                                         Ad_Pexp_construct_Da *) *)
(* (*                                                                                                                                         [ *) *)
(* (*                                                                                                                                           ident *) *)
(* (*                                                                                                                                             Ad_::_Da, *) *)
(* (*                                                                                                                                           process_generic_type *) *)
(* (*                                                                                                                                             Ad_expression_desc_Da *) *)
(* (*                                                                                                                                             Ad_Pexp_tuple_Da *) *)
(* (*                                                                                                                                             [ *) *)
(* (*                                                                                                                                               process_expression_list *) *)
(* (*                                                                                                                                                 [ *) *)
(* (*                                                                                                                                                   process_generic_type *) *)
(* (*                                                                                                                                                     Ad_expression_desc_Da *) *)
(* (*                                                                                                                                                     Ad_Pexp_apply_Da *) *)
(* (*                                                                                                                                                     [ *) *)
(* (*                                                                                                                                                       process_generic_type *) *)
(* (*                                                                                                                                                         Ad_expression_desc_Da *) *)
(* (*                                                                                                                                                         Ad_Pexp_ident_Da *) *)
(* (*                                                                                                                                                         [ *) *)
(* (*                                                                                                                                                           ident *) *)
(* (*                                                                                                                                                             Ad_process_core_type_list_Da *) *)
(* (*                                                                                                                                                         ], *) *)
(* (*                                                                                                                                                       process_arg_label_expression_list *) *)
(* (*                                                                                                                                                         [ *) *)
(* (*                                                                                                                                                           process_arg_label_expression *) *)
(* (*                                                                                                                                                             (process_generic_type *) *)
(* (*                                                                                                                                                               Ad_arg_label_Da *) *)
(* (*                                                                                                                                                               Ad_Nolabel_Da *) *)
(* (*                                                                                                                                                               Ad_None) *) *)
(* (*                                                                                                                                                             (process_generic_type *) *)
(* (*                                                                                                                                                               Ad_expression_desc_Da *) *)
(* (*                                                                                                                                                               Ad_Pexp_construct_Da *) *)
(* (*                                                                                                                                                               [ *) *)
(* (*                                                                                                                                                                 ident *) *)
(* (*                                                                                                                                                                   Ad_empty_list, *) *)
(* (*                                                                                                                                                                 none *) *)
(* (*                                                                                                                                                               ]) *) *)
(* (*                                                                                                                                                         ] *) *)
(* (*                                                                                                                                                     ], *) *)
(* (*                                                                                                                                                   process_generic_type *) *)
(* (*                                                                                                                                                     Ad_expression_desc_Da *) *)
(* (*                                                                                                                                                     Ad_Pexp_construct_Da *) *)
(* (*                                                                                                                                                     [ *) *)
(* (*                                                                                                                                                       ident *) *)
(* (*                                                                                                                                                         Ad_empty_list, *) *)
(* (*                                                                                                                                                       none *) *)
(* (*                                                                                                                                                     ] *) *)
(* (*                                                                                                                                                 ] *) *)
(* (*                                                                                                                                             ] *) *)
(* (*                                                                                                                                         ] *) *)
(* (*                                                                                                                                     ] *) *)
(* (*                                                                                                                                 ] *) *)
(* (*                                                                                                                             ]) *) *)
(* (*                                                                                                                       ] *) *)
(* (*                                                                                                                   ]) *) *)
(* (*                                                                                                             ] *) *)
(* (*                                                                                                         ]) *) *)
(* (*                                                                                                   ] *) *)
(* (*                                                                                               ]) *) *)
(* (*                                                                                         ] *) *)
(* (*                                                                                     ]) *) *)
(* (*                                                                               ] *) *)
(* (*                                                                           ]) *) *)
(* (*                                                                     ] *) *)
(* (*                                                                 ], *) *)
(* (*                                                               process_generic_type *) *)
(* (*                                                                 Ad_expression_desc_Da *) *)
(* (*                                                                 Ad_Pexp_construct_Da *) *)
(* (*                                                                 [ *) *)
(* (*                                                                   ident *) *)
(* (*                                                                     Ad_empty_list, *) *)
(* (*                                                                   none *) *)
(* (*                                                                 ] *) *)
(* (*                                                             ] *) *)
(* (*                                                         ] *) *)
(* (*                                                     ]) *) *)
(* (*                                               ] *) *)
(* (*                                           ], *) *)
(* (*                                         process_generic_type *) *)
(* (*                                           Ad_expression_desc_Da *) *)
(* (*                                           Ad_Pexp_construct_Da *) *)
(* (*                                           [ *) *)
(* (*                                             ident *) *)
(* (*                                               Ad_empty_list, *) *)
(* (*                                             none *) *)
(* (*                                           ] *) *)
(* (*                                       ] *) *)
(* (*                                   ] *) *)
(* (*                               ] *) *)
(* (*                           ] *) *)
(* (*                       ] *) *)
(* (*                   ]) *) *)
(* (*             ] *) *)
(* (*         ] *) *)
(* (*     ]. *) *)

(* End WithUniMath . *)

(* (* *)
(* : compare Universes.ContextSet.subsetP All_Forall.All2_fold_app_inv *)
(*   ctx_inst_impl All_Forall.All2_apply_dep_All All_Forall.OnOne2All_split *)
(*   All_Forall.OnOne2All_ind_l All_Forall.OnOne2All_exist *)
(*   MCRelations.clos_rt_t_incl CRelationClasses.PartialOrder_inverse *)
(*   Lists.foldr1_foldr1_map on_wf_global_env_impl_config *)
(*   All_Forall.Alli_All_mix MCRelations.clos_t_rt_incl *)
(*   All_Forall.All2_map2_left_All3 All_Forall.All2_mix_inv fold_rec_bis *)
(*   All_Forall.OnOne2i_impl_exist_and_All_r All_Forall.All_remove_last *)
(*   MCReflect.equiv_reflectT All_Forall.forallb_All cardinal_inv_2b *)
(*   All_Forall.All2_map_right_equiv All_Forall.All2_reflexivity *)
(*   List.Forall_rect All_Forall.All2_map_inv MCList.rev_ind PeanoNat.Nat.OddT_2 *)
(*   PeanoNat.Nat.OddT_1 fold_rec_nodep dirprod_hSet_subproof *)
(*   All_Forall.All2_right_triv univ_surj_unique infer_sort_impl *)
(*   All_Forall.All2_fold_All_fold_mix_left *)
(*   Universes.is_not_prop_and_is_not_sprop *)
(*   All_Forall.All2_fold_All_fold_mix_right MCList.list_rect_rev *)
(*   All_Forall.All2_fold_All_fold_mix_left_inv All_Forall.OnOne2i_nth_error_r *)
(*   All_Forall.All_fold_prod All_Forall.All_fold_impl natgthtogthm1 *)
(*   natgthtogehm1 All_Forall.OnOne2_sym All_Forall.OnOne2_map *)
(*   All_Forall.OnOne2_app All_Forall.All2i_app_inv *)
(*   All_Forall.All2_from_nth_error strictly_extends_decls_part_trans *)
(*   All_Forall.All2i_All_mix_right All_Forall.map_eq_inj *)
(*   All_Forall.All2i_len_impl All_Forall.Alli_rev_nth_error *)
(*   MCRelations.flip_Symmetric All_Forall.All2_nth_error_Some *)
(*   All_Forall.OnOne2_nth_error All_Forall.All2_All_left_pack *)
(*   on_global_env_impl_config ByteCompareSpec.reflect_equiv *)
(*   All_Forall.All_safe_nth All_Forall.All2_map2_right List.nth_in_or_default *)
(*   Universes.cuniv_sup_not_uproplevel All_Forall.All1_map2_right *)
(*   MCRelations.clos_rt_trans CRelationClasses.partial_order_antisym *)
(*   CRelationClasses.flip_PreOrder All_Forall.allbiP *)
(*   All_Forall.All_All2_swap_sum MCOption.nth_map_option_out *)
(*   extends_decls_part_refl All_Forall.All_map_inv All_Forall.All_map_All *)
(*   extends_decls_part_globals_trans *)
(* Ast.predicate_eq_dec *)
(*   All_Forall.All2_fold_app_inv_l All_Forall.Alli_shift *)
(*   All_Forall.All2_impl_In extends_decls_part_globals_refl univ_surj_ax *)
(*   MCRelations.relation_equivalence_inclusion All_Forall.All2_trans' *)
(*   PeanoNat.Nat.odd_OddT MCRelations.clos_t_rt strictly_extends_decls_trans *)
(*   All_Forall.All_Alli_swap_iff All_Forall.In_All *)
(*   strictly_extends_decls_extends_part_globals infer_typing_sort_impl *)
(*   All_Forall.All3_map_all ctx_inst_impl_gen PeanoNat.Nat.EvenT_OddT_rect *)
(*   extends_strictly_on_decls_l_merge *)
(*   StandardFiniteSets.partial_sum_slot_subproof Lists.Unnamed_thm3 *)
(*   Lists.Unnamed_thm2 Lists.Unnamed_thm1 Lists.Unnamed_thm0 *)
(*   All_Forall.All2_firstn CRelationClasses.relation_implication_preorder *)
(*   All_Forall.alli_Alli MCRelations.clos_t_rt_equiv *)
(*   All_Forall.All_fold_All2_fold_impl All_Forall.All2_All_mix_right *)
(*   All_Forall.OnOne2All_impl_exist_and_All_r *)
(*   All_Forall.OnOne2All_impl_exist_and_All All_Forall.All_fold_app_inv *)
(*   All_Forall.All_All2_All2_mix Lists.map_cons extends_r_merge *)
(*   All_Forall.All_All_All2 All_Forall.All2_apply_arrow *)
(*   MCOption.option_extendsT All_Forall.All2i_trivial BasicAst.All2_fold_map *)
(*   MCList.snocP MCRelations.clos_refl_trans_prod_r *)
(*   MCRelations.clos_refl_trans_prod_l MCRelations.clos_rt_monotone *)
(*   String.eqb_spec All_Forall.All_tip All_Forall.All_rev All_Forall.All_mix *)
(*   All_Forall.All_map All_Forall.All_app refine_type *)
(*   All_Forall.OnOne2_impl_exist_and_All_r All_Forall.Alli_rev *)
(*   All_Forall.Alli_mix All_Forall.Alli_app All_Forall.Alli_All *)
(*   All_Forall.All_refl All_Forall.All_prod All_Forall.All_pair *)
(*   All_Forall.All_mapi All_Forall.All_impl All_Forall.All_eta3 *)
(*   All_Forall.All_True Zeven.Zsplit2 All_Forall.All_Alli All_Forall.All_All2 *)
(*   List.exists_last All_Forall.All2_sym All_Forall.All2_rev *)
(*   All_Forall.All2_nth All_Forall.All2_mix All_Forall.All2_map *)
(*   All_Forall.All2_app All_Forall.All2_All BasicAst.All2_fold_mapi *)
(*   Universes.is_prop_and_is_sprop_val_false PeanoNat.Nat.EvenT_S_OddT *)
(*   extends_r_merge_globals BasicAst.All2_fold_cst_map *)
(*   extends_strictly_on_decls_trans All_Forall.All2_rect_rev *)
(*   All_Forall.All2_fold_All_swap All_Forall.All2_fold_All_left cardinal_inv_2 *)
(*   All_Forall.All_fold_app All_local_env_impl_ind BasicAst.def_eq_dec *)
(*   All_Forall.Alli_shiftn_inv All_Forall.All2_All_mix_left *)
(*   All_Forall.All2_nth_error_Some_r All_Forall.Alli_nth_error *)
(*   All_Forall.forall_nth_error_All StandardFiniteSets.eqtoweqstn_subproof2 *)
(*   StandardFiniteSets.eqtoweqstn_subproof1 *)
(*   StandardFiniteSets.eqtoweqstn_subproof0 All_Forall.forall_nth_error_Alli *)
(*   All_Forall.forallbP PeanoNat.Nat.OddT_S_EvenT *)
(*   All_Forall.OnOne2All_nth_error_r PeanoNat.Nat.Even_EvenT *)
(*   MCRelations.clos_rt_trans_Symmetric MCList.nth_nth_error' *)
(*   All_Forall.OnOne2All_nth_error_impl Universes.Level.eqb_spec *)
(*   BasicAst.All2_fold_impl_onctx All_Forall.All2_prod_inv plus_n_Sm *)
(*   All_Forall.All2i_rev_ctx isapropishinh All_Forall.Alli_mapi *)
(*   CRelationClasses.flip_Reflexive All_Forall.All2P Lists.foldr1_cons_nil *)
(*   BasicAst.fresh_evar_id ReflectEq.eqb_specT All_Forall.All_fold_Alli_rev *)
(*   extends_decls_extends All_Forall.forallb_nth' MCReflect.reflect_reflectT *)
(*   All_Forall.All_skipn All_Forall.forallb2P All_Forall.Alli_shiftn *)
(*   StandardFiniteSets.eqtoweqstn_subproof All_Forall.All2i_rev_ctx_inv *)
(*   All_Forall.All2i_rev_ctx_gen type_local_ctx_impl_gen *)
(*   CRelationClasses.flip_StrictOrder Lists.foldr1_cons All_Forall.Forall_All *)
(*   cstr_respects_variance_impl on_constructor_impl_config_gen *)
(*   List.destruct_list strictly_extends_decls_extends_part map_induction_min *)
(*   map_induction_max CRelationClasses.relation_equivalence_equivalence *)
(*   All_Forall.OnOne2_impl_All_r All_Forall.All2i_All_right *)
(*   PeanoNat.Nat.EvenT_OddT_dec Zpower.Zdiv_rest_correct *)
(*   All_Forall.All2i_mapi_rec strictly_extends_decls_part_globals_trans *)
(*   All_decls_alpha_pb_impl StandardFiniteSets.dualelement_lt *)
(*   All_Forall.All_fold_All2_fold All_Forall.All2i_map_right *)
(*   Lists.foldr1_map_nil strictly_extends_decls_part_globals_refl *)
(*   All_Forall.All2_map_left_equiv extends_strictly_on_decls_extends *)
(*   All_Forall.All2_transitivity All_Forall.OnOne2i_impl_exist_and_All *)
(*   All_Forall.OnOne2_All2_All2 map_induction *)
(*   Environment.Retroknowledge.extendsT Lists.map_nil *)
(*   All_Forall.All2i_All2_mix_left All_Forall.OnOne2_impl_exist_and_All *)
(*   cardinal_inv_2 MCRelations.relation_disjunction_refl_r *)
(*   MCRelations.relation_disjunction_refl_l All_Forall.All3_impl *)
(*   All_Forall.All2i_rev All_Forall.All2i_map All_Forall.All2i_app *)
(*   All_Forall.All2_symP All_Forall.All2_swap All_Forall.All2_same *)
(*   All_Forall.All2_refl All_Forall.All2_mapi All_Forall.All2_impl *)
(*   MCRelations.clos_rt_disjunction_right All_Forall.OnOne2i_All_mix_left *)
(*   extends_l_merge PeanoNat.Nat.even_EvenT All_Forall.All2_fold_trans *)
(*   All_Forall.All2i_nth_hyp strictly_extends_decls_l_merge_globals *)
(*   All_Forall.OnOne2All_nth_error All_Forall.All2_fold_nth_r fold_rel fold_rec *)
(*   All_Forall.All2_app_inv isweqtoforallpathsUAH *)
(*   All_Forall.OnOne2_All_mix_left extends_decls_refl *)
(*   All_Forall.All2i_All2_All2 BasicAst.onctxP All_Forall.All2i_Alli_mix_left *)
(*   Lists.foldr_cons All_Forall.OnOne2_nth_error_r Lists.foldr1_nil In_dec *)
(*   All_Forall.OnOne2All_sym All_Forall.OnOne2All_map All_Forall.OnOne2All_app *)
(*   All_Forall.All2i_mapi All_Forall.All2i_impl MCRelations.clos_rt_refl *)
(*   All_Forall.All2_symmetry All_Forall.All_nth_error All_Forall.All_repeat *)
(*   All_Forall.All1i_Alli_mix_left on_constructors_impl_config_gen *)
(*   All_Forall.Alli_app_inv All_Forall.forallbP_cond extends_refl *)
(*   Ascii.eqb_spec All_decls_to_alpha All_Forall.All2_undep *)
(*   All_Forall.All2_trans All_Forall.All2_skipn All_Forall.All2_right *)
(*   All_Forall.All2_eq_eq All_Forall.All2_apply All_Forall.All2_app_r *)
(*   All_Forall.All2i_All_left All_Forall.All_forall All_Forall.All_firstn *)
(*   ind_respects_variance_impl All_Forall.OnOne2All_All_mix_left *)
(*   All_Forall.All2i_nth_impl_gen strictly_extends_decls_refl *)
(*   All_Forall.All2_All_right All_Forall.All2_map_left MCOption.option_map_Some *)
(*   extends_strictly_on_decls_refl MCRelations.flip_Transitive *)
(*   extends_decls_part_trans lift_typing_impl fold_rec_weak *)
(*   MCRelations.clos_sym_Symmetric set_induction_min set_induction_max *)
(*   sorts_local_ctx_impl PeanoNat.Nat.OddT_EvenT_rect All_Forall.All2i_len_rev *)
(*   All_Forall.All2i_len_app MCReflect.reflectT_reflect *)
(*   All_Forall.All2_map_right All_Forall.All2_map_equiv *)
(*   All_Forall.forallb2_All2 All_Forall.Alli_rev_All_fold extends_trans *)
(*   Zeven.Z_modulo_2 All_Forall.All_All2_fold_swap_sum MCList.rev_case *)
(*   lift_judgment_impl Lists.foldr1_map_cons isaset_set_fun_space *)
(*   All_Forall.All2_fold_from_nth_error MCList.nth_error_spec *)
(*   MCOption.reflect_option_default BasicAst.ondeclP *)
(*   CRelationClasses.flip_Antisymmetric All_Forall.All2i_All_mix_left *)
(*   All_Forall.OnOne2_All_All fold_rel fold_rec All_Forall.OnOne2i_nth_error *)
(*   declared_ind_declared_constructors All_Forall.All_All2_fold_swap *)
(*   All_Forall.OnOne2i_mapP All_Forall.OnOne2i_impl extends_l_merge_globals *)
(*   CRelationClasses.flip_PER In_dec All_Forall.All2_apply_dep_arrow *)
(*   ZArith_dec.Z_notzerop cstr_respects_variance_impl_gen *)
(*   All_Forall.All2_map2_left MCRelations.clos_rt_disjunction_left *)
(*   set_induction StandardFiniteSets.stn_eq All_Forall.OnOne2_split *)
(*   All_Forall.OnOne2_ind_l All_Forall.OnOne2_exist All_Forall.OnOne2_app_r *)
(*   All_Forall.All2_map2_right_inv All_Forall.Forall2_All2 *)
(*   CRelationClasses.flip_Equivalence All_local_env_impl All_local_env_fold *)
(*   MCReflect.elimT All_Forall.All2_All_swap All_Forall.All2_All_left *)
(*   All_Forall.All2_All2_mix All_Forall.OnOne2i_sym All_Forall.OnOne2i_map *)
(*   All_Forall.OnOne2i_app Lists.foldr_nil All_Forall.OnOne2_mapP *)
(*   All_Forall.OnOne2_impl strictly_extends_decls_extends_decls *)
(*   All_Forall.All1_map2_right_inv All_Forall.All2i_app_inv_r *)
(*   All_Forall.All2i_app_inv_l All_Forall.OnOne2All_map_all *)
(*   All_Forall.OnOne2All_mapP All_Forall.OnOne2All_impl *)
(*   All_Forall.OnOne2All_All3 All_Forall.nth_error_alli *)
(*   All_Forall.All2i_map2_right set_induction_bis sorts_local_ctx_impl_gen *)
(*   ZArith_dec.Z_noteq_dec All_decls_alpha_impl All_Forall.All2_dep_nth_error *)
(*   MCOption.on_SomeP MCList.rev_list_ind extends_decls_trans fold_rec_weak *)
(*   strictly_extends_decls_part_refl All_Forall.Alli_All_fold *)
(*   All_Forall.map_option_Some map_induction_bis All_Forall.All2_fold_All_right *)
(*   fold_rec_bis cardinal_inv_2b All_Forall.All2_fold_sym *)
(*   All_Forall.All2_fold_nth All_Forall.All2_fold_app Lists.foldr1_map_cons_nil *)
(*   on_wf_global_env_impl PeanoNat.Nat.Odd_OddT natgthandplusm *)
(*   All_Forall.OnOne2i_split All_Forall.OnOne2i_ind_l All_Forall.OnOne2i_exist *)
(*   All_Forall.OnOne2i_app_r fold_rec_nodep All_decls_impl All_local_env_skipn *)
(*   All_Forall.All_prod_inv on_variance_impl Universes.ConstraintType.eq_dec *)
(*   All_Forall.Alli_rev_inv All_Forall.All2_fold_refl All_Forall.All2_fold_prod *)
(*   All_Forall.All2_fold_impl All_Forall.All2_fold_All2 *)
(*   StandardFiniteSets.weqfromcoprodofstn_eq2 *)
(*   StandardFiniteSets.weqfromcoprodofstn_eq1 *)
(*   CRelationClasses.subrelation_symmetric Ast.branch_eq_dec on_global_env_impl *)
(*   isaprop_isInjectiveFunction Uint63.ltbP Uint63.lebP Uint63.eqbP *)
(*   All_Forall.All2i_nth_error_r All_Forall.All2i_nth_error_l *)
(*   BasicAst.eqdec_binder_annot All_Forall.All2_fold_All_fold_mix natchoice0 *)
(*   All_Forall.All2_impl_All2 MCReflect.reflectT_pred *)
(*   MCRelations.flip_Reflexive MCRelations.iffT_l All_Forall.All_impl_All *)
(*   All_Forall.All2i_All2_All2i_All2i All_Forall.All2_nth_error_Some_right *)
(*   type_local_ctx_impl All_Forall.OnOne2All_All2_mix_left *)
(*   All_Forall.All2_fold_prod_inv All_Forall.All2_dep_from_nth_error *)
(*   Lists.Unnamed_thm MCList.nth_error_Some' PeanoNat.Nat.EvenT_2 *)
(*   PeanoNat.Nat.EvenT_0 All_Forall.map_option_out_All MCReflect.reflectT_pred2 *)
(*   All_Forall.All2_dep_impl All_Forall.All_rev_map All_Forall.All_rev_inv *)
(*   StandardFiniteSets.dualelement_0_empty All_Forall.All_All2_swap *)
(*   All_Forall.All_All2_refl All_Forall.All_All2_flex *)
(*   strictly_extends_decls_extends_strictly_on_decls *)
(*   All_Forall.All1i_map2_right MCRelations.relation_disjunction_Symmetric *)
(*   epiissurjectiontosets minusminusmmn All_Forall.OnOne2All_impl_All_r *)
(*   All_Forall.All2_fold_All_fold_mix_inv All_Forall.All2_fold_impl_len *)
(*   All_Forall.All2_fold_impl_ind MCReflect.reflectT_subrelation' *)
(*   All_Forall.All2_app_inv_r All_Forall.All2_app_inv_l. *)

(*  *) *)

(* From MetaCoq.Utils Require Import utils. *)
(* From MetaCoq.Template Require Import All. *)


(* MetaCoq Quote Recursively Definition ref_air := Datatypes.pair. *)
(* (* MetaCoq Test Quote Recursively Definition tConst. *) *)
(* (* MetaCoq Test Quote  Recursively MPfile. *) *)
(* (* MetaCoq Test Quote  Recursively tApp. *) *)
(* (* MetaCoq Test Quote  Recursively Datatypes.S. *) *)
(* (* MetaCoq Test Quote  Recursively tConstruct. *) *)
(* (* MetaCoq Test Quote  Recursively inductive_mind. *) *)
(* (* MetaCoq Test Quote  Recursively MetaCoq.Template.Ast.term. *) *)
(* (* MetaCoq Test Quote  Recursively MetaCoq.Common.Kernames.modpath. *) *)
(* (* MetaCoq Test Quote  Recursively Datatypes.O. *) *)
(* (* MetaCoq Test Quote  Recursively Datatypes.S. *) *)
(* (* MetaCoq Test Quote  Recursively Coq.Init.Datatypes.nat. *) *)

(* (* (tConst *) *)
(* (*    (Datatypes.pair (MPfile ["Ast"; "Template"; "MetaCoq"]) "predicate_eq_dec") *) *)
(* (*    []) *) *)
(* (* (tApp *) *)
(* (*    (tConst *) *)
(* (*       (Datatypes.pair (MPfile ["BasicAst"; "Common"; "MetaCoq"]) *) *)
(* (*          "All2_fold_map") []) *) *)
(* (*    [tEvar *) *)
(* (*       (Datatypes.S *) *)
(* (*          (Datatypes.S *) *)
(* (*             (Datatypes.S *) *)
(* (*                (Datatypes.S *) *)
(* (*                   (Datatypes.S *) *)
(* (*                      (Datatypes.S *) *)
(* (*                         (Datatypes.S *) *)
(* (*                            (Datatypes.S *) *)
(* (*                               (Datatypes.S *) *)
(* (*                                  (Datatypes.S *) *)
(* (*                                     (Datatypes.S *) *)
(* (*                                        (Datatypes.S *) *)
(* (*                                           (Datatypes.S *) *)
(* (*                                              (Datatypes.S *) *)
(* (*                                                 (Datatypes.S *) *)
(* (*                                                  (Datatypes.S *) *)
(* (*                                                  (Datatypes.S *) *)
(* (*                                                  (Datatypes.S *) *)
(* (*                                                  (Datatypes.S *) *)
(* (*                                                  (Datatypes.S *) *)
(* (*                                                  (Datatypes.S (...)))))))))))))))))))))) *) *)
(* (*       []; *) *)

(* (* MetaCoq Test Quote  Recursively  Ast.predicate_eq_dec. *) *)
(* (* MetaCoq Test Quote BasicAst.All2_fold_map. *) *)
(* (* MetaCoq Test Quote BasicAst.All2_fold_mapi. *) *)
(* (* MetaCoq Test Quote BasicAst.All2_fold_cst_map. *) *)
(* (* MetaCoq Test Quote BasicAst.All2_fold_impl_onctx. *) *)
(* (* MetaCoq Test Quote BasicAst.fresh_evar_id. *) *)
(* (* MetaCoq Test Quote BasicAst.onctxP . *) *)
(* (* MetaCoq Test Quote BasicAst.ondeclP. *) *)
(* (* MetaCoq Test Quote MyUU. *) *)
(* (* MetaCoq Test Quote Ast.branch_eq_dec. *) *)
(* (* MetaCoq Test Quote BasicAst.eqdec_binder_annot. *) *)

(* MetaCoq Quote  Recursively Definition reifMyUU := MyUU. *)
(* Print reifMyUU. *)

(* (* Definition process_ref x := x. *) *)
(*   (* match x.declarations with *) *)
(*   (* | a =>   a *) *)
(*   (* end. *) *)

(* (* Definition process_ref2 := process_ref reifMyUU. *)
(* Print process_ref2. *)
(*  *) *)








(* Recursive Extraction Library  All. *)
