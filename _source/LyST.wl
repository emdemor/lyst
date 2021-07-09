(* ::Package:: *)

(* ::Subsubtitle:: *)
(*LyST.m*)


(* ::Text:: *)
(*Eduardo M. de Morais*)
(*Instituto de F\[IAcute]sica Te\[OAcute]rica, Unesp,Brazil*)


(* ::Text:: *)
(**)


(*Print["LyraGravity.wl included."];*)


Notation`AutoLoadNotationPalette = False;
BeginPackage["LyST`",{"Notation`"}];

(* Red variable goes to black *)
SetOptions[$FrontEndSession,AutoStyleOptions->{"SymbolShadowingStyle"->{FontColor->Black}}]

(* This are the symbols used to designate up and down index *)
Unprotect[u,d];
ClearAll[u,d];
u=u;
d=d;
Protect[u,d];


(* ::Subsection:: *)
(*Functions*)


SubscriptNumber[ind_] := {"\:2080","\:2081","\:2082","\:2083","\:2084","\:2085","\:2086","\:2087","\:2088","\:2089"}[[ind+1]];
SuperscriptNumber[ind_] := {"\:2070","\.b9","\.b2","\.b3","\:2074","\:2075","\:2076","\:2077","\:2078","\:2079"}[[ind+1]];



(* ::Subsection:: *)
(*Notations*)


(* ::Text:: *)
(*Kroneceker Delta*)


Notation[ParsedBoxWrapper[SubsuperscriptBox["\[Delta]", "i_", "j_"]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"KroneckerDelta", "[", RowBox[{"i_", ",", "j_"}], "]"}]]]
Notation[ParsedBoxWrapper[SubscriptBox["\[Delta]", RowBox[{"i_", ",", "j_"}]]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"KroneckerDelta", "[", RowBox[{"i_", ",", "j_"}], "]"}]]]
Notation[ParsedBoxWrapper[SuperscriptBox["\[Delta]", RowBox[{"i_", ",", "j_"}]]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"KroneckerDelta", "[", RowBox[{"i_", ",", "j_"}], "]"}]]]


(* ::Text:: *)
(*Levi Civita Symbol*)


Notation[ParsedBoxWrapper[SubscriptBox["\[CurlyEpsilon]", RowBox[{"i_", ",", "j_", ",", "k_"}]]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{RowBox[{"LeviCivitaTensor", "[", "3", "]"}], "[", RowBox[{"[", RowBox[{"i_", ",", "j_", ",", "k_"}], "]"}], "]"}]]]
Notation[ParsedBoxWrapper[SuperscriptBox["\[CurlyEpsilon]", RowBox[{"i_", ",", "j_", ",", "k_"}]]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{RowBox[{"LeviCivitaTensor", "[", "3", "]"}], "[", RowBox[{"[", RowBox[{"i_", ",", "j_", ",", "k_"}], "]"}], "]"}]]]
Notation[ParsedBoxWrapper[SubscriptBox["\[CurlyEpsilon]", RowBox[{"i_", ",", "j_", ",", "k_", ",", "l_"}]]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{RowBox[{"LeviCivitaTensor", "[", "4", "]"}], "[", RowBox[{"[", RowBox[{RowBox[{"1", "+", "i_"}], ",", RowBox[{"1", "+", "j_"}], ",", RowBox[{"1", "+", "k_"}], ",", RowBox[{"1", "+", "l_"}]}], "]"}], "]"}]]]
Notation[ParsedBoxWrapper[SuperscriptBox["\[CurlyEpsilon]", RowBox[{"i_", ",", "j_", ",", "k_", ",", "l_"}]]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{RowBox[{"LeviCivitaTensor", "[", "4", "]"}], "[", RowBox[{"[", RowBox[{RowBox[{"1", "+", "i_"}], ",", RowBox[{"1", "+", "j_"}], ",", RowBox[{"1", "+", "k_"}], ",", RowBox[{"1", "+", "l_"}]}], "]"}], "]"}]]]




(* ::Text:: *)
(*Usefull Symbols*)


Symbolize[ParsedBoxWrapper[SubscriptBox[OverscriptBox["g", "_"], GridBox[{{"i_", "j_"}}]]] ]
Symbolize[ParsedBoxWrapper[SubscriptBox["x_", "ind_"]],WorkingForm->TraditionalForm];
Symbolize[ParsedBoxWrapper[SuperscriptBox["x", "ind_"]],WorkingForm->TraditionalForm];(* From here, x^2 is different of (x)^2 *)
Symbolize[ParsedBoxWrapper[SubscriptBox["\[DoubleStruckG]", "\[Mu]_"]]];
Symbolize[ParsedBoxWrapper[SuperscriptBox["\[DoubleStruckG]", "\[Mu]_"]]];Symbolize[ParsedBoxWrapper[SqrtBox[RowBox[{"-", "g"}]]]];


$Assumptions={};
MakeAssumption[list`var_List]:=AppendTo[$Assumptions,#]&/@list`var;


(* ::Subsection:: *)
(*Define Scale Function*)


Unprotect[\[CapitalPhi]];
ClearAll[\[CapitalPhi],CheckScale];

CheckScale = False;

DefineScaleFunction[\[CapitalPhi]var_]:=Block[{},
Unprotect[\[CapitalPhi]];
ClearAll[\[CapitalPhi]];
\[CapitalPhi] = \[CapitalPhi]var;
CheckScale = True;
Protect[\[CapitalPhi]];
];

ErrorScaleMessage := If[!CheckCoordinates,Print["Error. You must define scale function first."]];


(* ::Subsection:: *)
(*Define Coordinates*)


Unprotect[\[DoubleStruckX],\[DoubleStruckCapitalX],x,X,CheckCoordinates];
ClearAll[\[DoubleStruckX],\[DoubleStruckCapitalX],x,X,CheckCoordinates];

CheckCoordinates = False;

DefineCoordinates[\[DoubleStruckCapitalX]`var_]:=Block[{},
Unprotect[\[DoubleStruckCapitalX],x,CheckCoordinates];
ClearAll[\[DoubleStruckCapitalX],x,CheckCoordinates];

\[DoubleStruckCapitalX]=\[DoubleStruckCapitalX]`var;
\[DoubleStruckX][in_]:=\[DoubleStruckCapitalX][[1+in]];
Notation[ParsedBoxWrapper[SuperscriptBox["x", "i_"]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"\[DoubleStruckCapitalX]", "[", RowBox[{"[", RowBox[{"i_", "+", "1"}], "]"}], "]"}]]];
Notation[ParsedBoxWrapper[RowBox[{SubscriptBox["\[PartialD]", "n_"], "Func_"}]] \[DoubleLongRightArrow] ParsedBoxWrapper[RowBox[{"Simplify", "[", RowBox[{"D", "[", RowBox[{"Func_", ",", RowBox[{"\[DoubleStruckCapitalX]", "[", RowBox[{"[", RowBox[{"n_", "+", "1"}], "]"}], "]"}]}], "]"}], "]"}]]];
Notation[ParsedBoxWrapper[RowBox[{SubscriptBox["\[PartialD]", "n_"], RowBox[{"[", "Func_", "]"}]}]] \[DoubleLongRightArrow] ParsedBoxWrapper[RowBox[{"Simplify", "[", RowBox[{"D", "[", RowBox[{"Func_", ",", RowBox[{"\[DoubleStruckCapitalX]", "[", RowBox[{"[", RowBox[{"n_", "+", "1"}], "]"}], "]"}]}], "]"}], "]"}]]];






CheckCoordinates  = True;
Protect[\[DoubleStruckCapitalX],x,CheckCoordinates];
];

ErrorCoordinatesMessage := If[!CheckCoordinates,Print["Error. You must define coordinates first."]];




(* ::Subsection:: *)
(*Define Metric*)


Unprotect[n,g,MetricCovM,MetricDet,MetricCon,CheckMetric];
ClearAll[n,g,MetricCovM,MetricDet,MetricCon,CheckMetric];
CheckMetric  = False;

DefineMetric[gMatrix_]:=Block[{},

ErrorCoordinatesMessage;

If[CheckCoordinates,
Unprotect[n,g,MetricCovM,MetricDet,MetricConM,CheckMetric];
ClearAll[n,g,MetricCovM,MetricDet,MetricConM,CheckMetric];
MetricCovM=gMatrix;
MetricCov[\[Mu]_,\[Alpha]_]:=MetricCovM[[\[Mu]+1,\[Alpha]+1]];
Notation[ParsedBoxWrapper[SubscriptBox["g", GridBox[{{"i_", "j_"}}]]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{RowBox[{"MetricCovM", "[", RowBox[{"[", RowBox[{"i_", "+", "1"}], "]"}], "]"}], "[", RowBox[{"[", RowBox[{"j_", "+", "1"}], "]"}], "]"}]]];
AddInputAlias["metriccov"->ParsedBoxWrapper[SubscriptBox["g", GridBox[{{"\[Placeholder]", "\[Placeholder]"}}]]]];
n=Length[MetricCovM]-1;
MetricDet = Det[MetricCovM]//FullSimplify;
Notation[ParsedBoxWrapper[SqrtBox[RowBox[{"-", "g"}]]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"Simplify", "[", RowBox[{SqrtBox[RowBox[{"-", "MetricDet"}]], ",", "$Assumptions"}], "]"}]]];
g = MetricDet;
MetricConM=Expand[Inverse[MetricCovM]];
MetricCon[\[Mu]_,\[Alpha]_]:=MetricConM[[\[Mu]+1,\[Alpha]+1]];
Notation[ParsedBoxWrapper[SuperscriptBox["g", GridBox[{{"i_", "j_"}}]]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{RowBox[{"MetricConM", "[", RowBox[{"[", RowBox[{"i_", "+", "1"}], "]"}], "]"}], "[", RowBox[{"[", RowBox[{"j_", "+", "1"}], "]"}], "]"}]]]
AddInputAlias["metriccon"->ParsedBoxWrapper[SuperscriptBox["g", GridBox[{{"\[Placeholder]", "\[Placeholder]"}}]]]];
CheckMetric = True;
Protect[n,g,MetricCovM,MetricDet,MetricConM,CheckMetric];
];



];

ErrorMetricMessage := If[!CheckMetric,Print["Error. You must define the metric first."]];



(* ::Subsection:: *)
(*Define Christoffel*)


Unprotect[ChristoffelM,Christoffel,CheckChristoffel];
ClearAll[ChristoffelM,Christoffel,CheckChristoffel];

CheckChristoffel = False;

DefineChristoffel[]:=Block[{},

ErrorCoordinatesMessage;
ErrorMetricMessage;
If[And[CheckCoordinates,CheckMetric],
Unprotect[ChristoffelM,Christoffel,CheckChristoffel];
ClearAll[ChristoffelM,Christoffel,CheckChristoffel];

ChristoffelM=Monitor[Table[Expand[Sum[1/2 MetricConM[[\[ScriptB]+1,\[ScriptA]+1]]
(D[MetricCovM[[\[ScriptE]+1,\[ScriptA]+1]],\[DoubleStruckCapitalX][[\[ScriptM]+1]]]+D[MetricCovM[[\[ScriptM]+1,\[ScriptA]+1]],\[DoubleStruckCapitalX][[\[ScriptE]+1]]]-D[MetricCovM[[\[ScriptM]+1,\[ScriptE]+1]],\[DoubleStruckCapitalX][[\[ScriptA]+1]]]),{\[ScriptA],0,n}]],{\[ScriptB],0,n},{\[ScriptM],0,n},{\[ScriptE],0,n}],Grid[{{"\[Beta]: ",\[ScriptB]},{"\[Mu]: ",\[ScriptM]},{"\[Epsilon]: ",\[ScriptE]}}]];


Christoffel[\[Mu]_,\[Alpha]_,\[Beta]_]:=ChristoffelM[[\[Mu]+1,\[Alpha]+1,\[Beta]+1]];

Notation[ParsedBoxWrapper[RowBox[{"{", GridBox[{{"\[Mu]_"}, {GridBox[{{"\[Alpha]_", "\[Beta]_"}}]}}], "}"}]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"Christoffel", "[", RowBox[{"\[Mu]_", ",", "\[Alpha]_", ",", "\[Beta]_"}], "]"}]]];

AddInputAlias["chris"->ParsedBoxWrapper[RowBox[{"{", GridBox[{{"\[Placeholder]"}, {GridBox[{{"\[Placeholder]", "\[Placeholder]"}}]}}], "}"}]]];

CheckChristoffel = True;
Protect[ChristoffelM,Christoffel,CheckChristoffel];

];

];

ErrorChristoffelMessage := If[!CheckChristoffel,Print["Error. You must define Christoffel symbols first."]];



(* ::Subsection:: *)
(*Define Connection*)


Unprotect[ConnectionM,Connection,CheckConnection];
ClearAll[ConnectionM,Connection,CheckConnection];

CheckConnection = False;

DefineConnection[]:=Block[{},

ErrorCoordinatesMessage;
ErrorMetricMessage;
ErrorChristoffelMessage;
If[And[CheckCoordinates,CheckMetric,CheckChristoffel],
Unprotect[ConnectionM,Connection,CheckConnection];
ClearAll[ConnectionM,Connection,CheckConnection];

PrintTemporary["\n\nEvaluating Connection..."];
ConnectionM=Monitor[Table[Expand[1/\[CapitalPhi] Christoffel[\[ScriptB],\[ScriptM],\[ScriptE]]+1/\[CapitalPhi]^2 (D[\[CapitalPhi],\[DoubleStruckCapitalX][[\[ScriptM]+1]]] \!\(\*SubsuperscriptBox[\(\[Delta]\), \(\[ScriptE]\), \(\[ScriptB]\)]\)-\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(\[ScriptL] = 0\), \(n\)]\(MetricConM[\([\[ScriptB] + 1, \[ScriptL] + 1]\)] MetricCovM[\([\[ScriptM] + 1, \[ScriptE] + 1]\)] D[\[CapitalPhi], \[DoubleStruckCapitalX][\([\[ScriptL] + 1]\)]]\)\))],{\[ScriptB],0,n},{\[ScriptM],0,n},{\[ScriptE],0,n}],Grid[{{"\[Beta]: ",\[ScriptB]},{"\[Mu]: ",\[ScriptM]},{"\[Epsilon]: ",\[ScriptE]}}]];



Connection[\[ScriptM]_,\[ScriptA]_,\[ScriptB]_]:=ConnectionM[[\[ScriptM]+1,\[ScriptA]+1,\[ScriptB]+1]];

Notation[ParsedBoxWrapper[SubsuperscriptBox["\[CapitalGamma]", RowBox[{"   ", GridBox[{{"\[Alpha]_", "\[Beta]_"}}]}], "\[Mu]_"]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"Connection", "[", RowBox[{"\[Mu]_", ",", "\[Alpha]_", ",", "\[Beta]_"}], "]"}]]];
AddInputAlias["conn"->ParsedBoxWrapper[SubsuperscriptBox["\[CapitalGamma]", RowBox[{"   ", GridBox[{{"\[Placeholder]", "\[Placeholder]"}}]}], "\[Placeholder]"]]];

CheckConnection = True;
Protect[ConnectionM,Connection,CheckConnection];

];

];
ErrorConnectionMessage := If[!CheckChristoffel,Print["Error. You must define Connection first."]];






(* ::Subsection:: *)
(*Define Curvature*)


Unprotect[CurvatureM,Curvature,CheckCurvature];
ClearAll[CurvatureM,Curvature,CheckCurvature];

CheckConnection = False;

DefineCurvature[]:=Block[{},

ErrorScaleMessage;
ErrorCoordinatesMessage;
ErrorMetricMessage;
ErrorChristoffelMessage;
ErrorConnectionMessage;


If[And[CheckScale,CheckCoordinates,CheckMetric,CheckChristoffel,CheckConnection],
Unprotect[CurvatureM,Curvature,CheckCurvature];
ClearAll[CurvatureM,Curvature,CheckCurvature];

(************************************************)
(* Christoffel Curvature Tensor *)
PrintTemporary["\n\nEvaluating Christoffel Curvature..."];
ChristoffelCurvatureTensorM=Monitor[Table[
Expand[D[Christoffel[\[ScriptM],\[ScriptL],\[ScriptB]],\[DoubleStruckX][\[ScriptA]]]-D[Christoffel[\[ScriptM],\[ScriptL],\[ScriptA]],\[DoubleStruckX][\[ScriptB]]]+
+Sum[Christoffel[\[ScriptM],\[ScriptR],\[ScriptA]]Christoffel[\[ScriptR],\[ScriptL],\[ScriptB]]-Christoffel[\[ScriptM],\[ScriptR],\[ScriptB]]Christoffel[\[ScriptR],\[ScriptL],\[ScriptA]],{\[ScriptR],0,n}]]
,{\[ScriptM],0,3},{\[ScriptL],0,3},{\[ScriptA],0,3},{\[ScriptB],0,3}],Grid[{{" Christoffel Curvature Tensor - \!\(\*SubscriptBox[SuperscriptBox[\(R\), \(\[Mu]\)], \(\[Lambda]\[Alpha]\[Beta]\)]\) "},{"\[Mu]: ",\[ScriptM]},{"\[Lambda]: ",\[ScriptL]},{"\[Alpha]: ",\[ScriptA]},{"\[Beta]: ",\[ScriptB]}}]];
ChristoffelCurvatureTensor[\[ScriptS]_,\[ScriptN]_,\[ScriptM]_,\[ScriptA]_]:=ChristoffelCurvatureTensorM[[1+\[ScriptS],1+\[ScriptN],1+\[ScriptM],1+\[ScriptA]]];
Notation[ParsedBoxWrapper[SubsuperscriptBox["\[ScriptCapitalR]", GridBox[{{" ", "\[ScriptN]_", "\[ScriptM]_", "\[ScriptA]_"}}], "\[ScriptS]_"]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"ChristoffelCurvatureTensorM", "[", RowBox[{"[", RowBox[{RowBox[{"1", "+", "\[ScriptS]_"}], ",", RowBox[{"1", "+", "\[ScriptN]_"}], ",", RowBox[{"1", "+", "\[ScriptM]_"}], ",", RowBox[{"1", "+", "\[ScriptA]_"}]}], "]"}], "]"}]]];

(************************************************)
(* Curvature Tensor *)
PrintTemporary["\n\nEvaluating Curvature Tensor..."];
CurvatureTensorM=Monitor[Table[
Expand[
1/\[CapitalPhi]^2 D[\[CapitalPhi] Connection[\[ScriptM],\[ScriptL],\[ScriptB]],\[DoubleStruckX][\[ScriptA]]]-1/\[CapitalPhi]^2 D[\[CapitalPhi] Connection[\[ScriptM],\[ScriptL],\[ScriptA]],\[DoubleStruckX][\[ScriptB]]]+
+Sum[Connection[\[ScriptM],\[ScriptR],\[ScriptA]]Connection[\[ScriptR],\[ScriptL],\[ScriptB]]-Connection[\[ScriptM],\[ScriptR],\[ScriptB]]Connection[\[ScriptR],\[ScriptL],\[ScriptA]],{\[ScriptR],0,n}]]
,{\[ScriptM],0,3},{\[ScriptL],0,3},{\[ScriptA],0,3},{\[ScriptB],0,3}],Grid[{{" Curvature Tensor - \!\(\*SubscriptBox[SuperscriptBox[\(R\), \(\[Mu]\)], \(\[Lambda]\[Alpha]\[Beta]\)]\) "},{"\[Mu]: ",\[ScriptM]},{"\[Lambda]: ",\[ScriptL]},{"\[Alpha]: ",\[ScriptA]},{"\[Beta]: ",\[ScriptB]}}]];
CurvatureTensor[\[ScriptS]_,\[ScriptN]_,\[ScriptM]_,\[ScriptA]_]:=CurvatureTensorM[[1+\[ScriptS],1+\[ScriptN],1+\[ScriptM],1+\[ScriptA]]];
Notation[ParsedBoxWrapper[SubsuperscriptBox["R", GridBox[{{" ", "\[ScriptN]_", "\[ScriptM]_", "\[ScriptA]_"}}], "\[ScriptS]_"]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"CurvatureTensorM", "[", RowBox[{"[", RowBox[{RowBox[{"1", "+", "\[ScriptS]_"}], ",", RowBox[{"1", "+", "\[ScriptN]_"}], ",", RowBox[{"1", "+", "\[ScriptM]_"}], ",", RowBox[{"1", "+", "\[ScriptA]_"}]}], "]"}], "]"}]]];

(************************************************)
(* Contracting curvature with Metric *)
If[True,
(* Covariant components of curvature tensor *)
CurvatureTensorCovM = Monitor[Table[
Expand[Sum[MetricCov[\[ScriptR],\[ScriptM]]CurvatureTensor[\[ScriptR],\[ScriptN],\[ScriptA],\[ScriptB]],{\[ScriptR],0,n}]]
,{\[ScriptM],0,3},{\[ScriptN],0,3},{\[ScriptA],0,3},{\[ScriptB],0,3}],Grid[{{" Curvature Subscript[K, \[Mu]\[Nu]\[Alpha]\[Beta]] "},{"\[Mu]: ",\[ScriptM]},{"\[Nu]: ",\[ScriptN]},{"\[Alpha]: ",\[ScriptA]},{"\[Beta]: ",\[ScriptB]}}]];
CurvatureTensorCov[\[ScriptA]_,\[ScriptB]_,\[ScriptC]_,\[ScriptD]_] := CurvatureTensorConM [[1+\[ScriptA],1+\[ScriptB],1+\[ScriptC],1+\[ScriptD]]];
Notation[ParsedBoxWrapper[RowBox[{SubscriptBox["R", GridBox[{{"\[ScriptM]_", "\[ScriptN]_", "\[ScriptA]_", "\[ScriptB]_"}}]], " "}]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{" ", RowBox[{"CurvatureTensorCovM", "[", RowBox[{"[", RowBox[{RowBox[{"1", "+", "\[ScriptM]_"}], ",", RowBox[{"1", "+", "\[ScriptN]_"}], ",", RowBox[{"1", "+", "\[ScriptA]_"}], ",", RowBox[{"1", "+", "\[ScriptB]_"}]}], "]"}], "]"}]}]]];
(*
(* Contravariant components of curvature tensor *)
CurvatureTensorConM = Table[
Expand[\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(\[ScriptA] = 0\), \(n\)]\(
\*UnderoverscriptBox[\(\[Sum]\), \(\[ScriptB] = 0\), \(n\)]\(
\*UnderoverscriptBox[\(\[Sum]\), \(\[ScriptC] = 0\), \(n\)]CurvatureTensor[\[ScriptM], \[ScriptA], \[ScriptB], \[ScriptC]]MetricCon[\[ScriptA], \[ScriptN]]MetricCon[\[ScriptB], \[ScriptP]]MetricCon[\[ScriptC], \[ScriptQ]]\)\)\)]
,{\[ScriptM],0,3},{\[ScriptN],0,3},{\[ScriptP],0,3},{\[ScriptQ],0,3}];

CurvatureTensorCon[a_,b_,c_,d_] := CurvatureTensorConM [[1+a,1+b,1+c,1+d]];
Notation[R^\[ScriptM]_	\[ScriptN]_	\[ScriptP]_	\[ScriptQ]_ \[DoubleLongLeftRightArrow] CurvatureTensorConM[[1+\[ScriptM]_,1+\[ScriptN]_,1+\[ScriptP]_,1+\[ScriptQ]_]]];*)

];


(************************************************)
(*  Ricci-Christoffel tensor Subscript[R, \[Mu]\[Sigma]] *)
PrintTemporary["\n\nEvaluating Ricci-Christoffel Tensor..."];
ChristoffelRicciCovM=Monitor[Table[Expand[\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(\[ScriptT] = 0\), \(n\)]\(ChristoffelCurvatureTensor[\[ScriptT], \[ScriptN], \[ScriptA], \[ScriptT]]\)\)],{\[ScriptN],0,3},{\[ScriptA],0,3}],Grid[{{" Ricci \!\(\*SubscriptBox[\(R\), \(\[Nu]\[Alpha]\)]\) "},{"\[Nu]: ",\[ScriptN]},{"\[Alpha]: ",\[ScriptA]}}]];
ChristoffelRicciCov[\[ScriptA]_,\[ScriptB]_]:=ChristoffelRicciCovM[[1+\[ScriptA],1+\[ScriptB]]];
Notation[ParsedBoxWrapper[SubscriptBox["\[ScriptCapitalR]", GridBox[{{"\[Alpha]_", "\[Beta]_"}}]]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"ChristoffelRicciCovM", "[", RowBox[{"[", RowBox[{RowBox[{"1", "+", "\[Alpha]_"}], ",", RowBox[{"1", "+", "\[Beta]_"}]}], "]"}], "]"}]]];


(************************************************)
(*  Ricci tensor Subscript[R, \[Mu]\[Sigma]] *)
PrintTemporary["\n\nEvaluating Ricci Tensor..."];
RicciCovM=Monitor[Table[Expand[\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(\[ScriptT] = 0\), \(n\)]\(CurvatureTensor[\[ScriptT], \[ScriptN], \[ScriptA], \[ScriptT]]\)\)],{\[ScriptN],0,3},{\[ScriptA],0,3}],Grid[{{" Ricci \!\(\*SubscriptBox[\(R\), \(\[Nu]\[Alpha]\)]\) "},{"\[Nu]: ",\[ScriptN]},{"\[Alpha]: ",\[ScriptA]}}]];
RicciCov[\[ScriptA]_,\[ScriptB]_]:=RicciCovM[[1+\[ScriptA],1+\[ScriptB]]];
Notation[ParsedBoxWrapper[SubscriptBox["R", GridBox[{{"\[Alpha]_", "\[Beta]_"}}]]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"RicciCovM", "[", RowBox[{"[", RowBox[{RowBox[{"1", "+", "\[Alpha]_"}], ",", RowBox[{"1", "+", "\[Beta]_"}]}], "]"}], "]"}]]];


(************************************************)
(*  Mixed Ricci-Christoffel tensor Subscript[R, \[Mu]\[Sigma]] *)
ChristoffelRicciMixM=Monitor[Table[Expand[\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(\[ScriptA] = 0\), \(n\)]\(MetricCon[\[ScriptS], \[ScriptA]] ChristoffelRicciCov[\[ScriptA], \[ScriptM]]\)\)],{\[ScriptS],0,3},{\[ScriptM],0,3}],Grid[{{" Ricci \!\(\*SubsuperscriptBox[\(R\), GridBox[{
{\(\\\ \), \(\[Mu]\)}
}], GridBox[{
{\(\[Sigma]\), \(\\\ \)}
}]]\)"},{"\[Sigma]: ",\[ScriptS]},{"\[Mu]: ",\[ScriptM]}}]];
ChristoffelRicciMix[\[ScriptA]_,\[ScriptB]_]:=ChristoffelRicciMixM[[1+\[ScriptA],1+\[ScriptB]]];
Notation[ParsedBoxWrapper[SubsuperscriptBox["\[ScriptCapitalR]", "\[Mu]_", "\[Sigma]_"]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"ChristoffelRicciMixM", "[", RowBox[{"[", RowBox[{RowBox[{"1", "+", "\[Sigma]_"}], ",", RowBox[{"1", "+", "\[Mu]_"}]}], "]"}], "]"}]]];


(************************************************)
(*  MixedRicci tensor Subscript[R, \[Mu]\[Sigma]] *)
RicciMixM=Monitor[Table[Expand[\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(\[ScriptA] = 0\), \(n\)]\(MetricCon[\[ScriptS], \[ScriptA]] RicciCov[\[ScriptA], \[ScriptM]]\)\)],{\[ScriptS],0,3},{\[ScriptM],0,3}],Grid[{{" Ricci \!\(\*SubsuperscriptBox[\(R\), GridBox[{
{\(\\\ \), \(\[Mu]\)}
}], GridBox[{
{\(\[Sigma]\), \(\\\ \)}
}]]\)"},{"\[Sigma]: ",\[ScriptS]},{"\[Mu]: ",\[ScriptM]}}]];
RicciMix[\[ScriptA]_,\[ScriptB]_]:=RicciMixM[[1+\[ScriptA],1+\[ScriptB]]];
Notation[ParsedBoxWrapper[SubsuperscriptBox["R", "\[Mu]_", "\[Sigma]_"]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"RicciMixM", "[", RowBox[{"[", RowBox[{RowBox[{"1", "+", "\[Sigma]_"}], ",", RowBox[{"1", "+", "\[Mu]_"}]}], "]"}], "]"}]]];




(************************************************)
(*  Christoffel Curvature Scalar R *)
PrintTemporary["\n\nEvaluating Christoffel Curvature Scalar..."];
\[ScriptCapitalR] =Expand[ \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(\[ScriptA] = 0\), \(n\)]\(ChristoffelRicciMix[\[ScriptA], \[ScriptA]]\)\)];


(************************************************)
(*  Curvature Scalar R *)
PrintTemporary["\n\nEvaluating Curvature Scalar..."];
R =Expand[ \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(\[ScriptA] = 0\), \(n\)]\(RicciMix[\[ScriptA], \[ScriptA]]\)\)];


(************************************************)
(*  Einstein tensor Subscript[G, \[Mu]\[Sigma]] *)
PrintTemporary["\n\nEvaluating Einstein Tensor..."];
EinsteinCovM = Expand[RicciCovM - 1/2 MetricCovM R ];
EinsteinCov[\[ScriptA]_,\[ScriptB]_]:=EinsteinCovM[[1+\[ScriptA],1+\[ScriptB]]];
Notation[ParsedBoxWrapper[SubscriptBox["G", GridBox[{{"\[Alpha]_", "\[Beta]_"}}]]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"EinsteinCovM", "[", RowBox[{"[", RowBox[{RowBox[{"1", "+", "\[Alpha]_"}], ",", RowBox[{"1", "+", "\[Beta]_"}]}], "]"}], "]"}]]];


CheckCurvature = True;
Protect[CurvatureM,Curvature,CheckCurvature];

];

];


ErrorChristoffelMessage := If[!CheckChristoffel,Print["Error. You must define Christoffel symbols first."]];


(* ::Subsection:: *)
(*Covariant Derivative of Tensors*)


Unprotect[CovD]
ClearAll[CovD]
CovD[strT_,pos_]:=Block[{(*var,\[GothicCapitalC]=Dimensions[strT],\[GothicCapitalA]=Length[Dimensions[strT]],\[GothicCapitalB]=Length[pos],\[GothicCapitalD],\[GothicCapitalR],\[GothicCapitalS]*)var0},

\[GothicCapitalC]=Dimensions[strT];\[GothicCapitalA]=Length[Dimensions[strT]];\[GothicCapitalB]=Length[pos];

If[\[GothicCapitalA]===\[GothicCapitalB],
CovIndex = {};
ConIndex = {};
Do[
If[pos[[i]]===u,AppendTo[ConIndex,i]];
If[pos[[i]]===d,AppendTo[CovIndex,i]];
,{i,1,Length[pos]}];


VarList = Table[ToExpression["var"<>ToString[i]],{i,1,\[GothicCapitalB]}];

\[GothicCapitalD] = Table[{var= ToExpression["var"<>ToString[i]],1,1+n},{i,1,\[GothicCapitalB]}];


Table[

\[GothicCapitalR]=Table[ToExpression["var"<>ToString[i]],{i,1,\[GothicCapitalB]}];
\[GothicCapitalS]=Part[strT,Evaluate[Sequence@@\[GothicCapitalR]] ];


1/\[CapitalPhi] D[\[GothicCapitalS],\[DoubleStruckCapitalX][[var0]]]

+

(Sum[

Sum[
ConnectionM[[VarList[[ind]],v,var0]]
strT[[Evaluate[Sequence@@ReplacePart[VarList,ind->v]]]]
,{v,1,n+1}]

,{ind,ConIndex}]+

Sum[

-Sum[
ConnectionM[[v,VarList[[ind]],var0]]
strT[[Evaluate[Sequence@@ReplacePart[VarList,ind->v]]]]
,{v,1,n+1}]

,{ind,CovIndex}])//Expand

,Evaluate[Sequence@@Join[{{var0,1,4}},\[GothicCapitalD]]]]


]]

Protect[CovD]



(* ::Chapter:: *)
(*The End*)


Begin["`Private`"];
End[] (* Private *) ;

Print[Style["LyST, v.00 ."]]
Print[Style["\t\t\tThis package is under construction. Be carefull.", Italic]]

EndPackage[];






