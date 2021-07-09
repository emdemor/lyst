#!/usr/bin/env wolframscript
(* ::Package:: *)

(* ::Title:: *)
(*LyST - Weak Field Equations *)


Notation`AutoLoadNotationPalette = False;
Needs["Notation`"]

(* Red variable goes to black *)
SetOptions[$FrontEndSession,AutoStyleOptions->{"SymbolShadowingStyle"->{FontColor->Black}}]

(* This are the symbols used to designate up and down index *)
Unprotect[u,d];
ClearAll[u,d];
u=u;
d=d;
Protect[u,d];


Off[Symbolize::bsymbexs]


(* ::Subsection:: *)
(*Standard Values*)


SetDimension[Dim_]:=Block[{},
	\[DoubleStruckCapitalD] = Dim;
	n = \[DoubleStruckCapitalD]-1;
]

SetDimension[4]

(* Minkowski Metric *)
MinkCov=MinkCon=
Table[
If[i!=j,0,
	If[i==1,1,-1]
],{i,1,\[DoubleStruckCapitalD]},{j,1,\[DoubleStruckCapitalD]}];



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



(* Defining coordinates *)
Symbolize[ParsedBoxWrapper[SubscriptBox["x_", "ind_"]],WorkingForm->TraditionalForm];
Symbolize[ParsedBoxWrapper[SuperscriptBox["x", "ind_"]],WorkingForm->TraditionalForm];(* A partir daqui, x^2 \[EAcute] diferente de (x)^2 *)

Symbolize[ParsedBoxWrapper[SubscriptBox["\[DoubleStruckG]", "\[Mu]_"]]];
Symbolize[ParsedBoxWrapper[SuperscriptBox["\[DoubleStruckG]", "\[Mu]_"]]];
Symbolize[ParsedBoxWrapper[SqrtBox[RowBox[{"-", "g"}]]]];


$Assumptions={};
MakeAssumption[list`var_List]:=AppendTo[$Assumptions,#]&/@list`var;


(* ::Subsection:: *)
(*Functions*)


SubscriptNumber[ind_] := {"\:2080","\:2081","\:2082","\:2083","\:2084","\:2085","\:2086","\:2087","\:2088","\:2089"}[[ind+1]];
SuperscriptNumber[ind_] := {"\:2070","\.b9","\.b2","\.b3","\:2074","\:2075","\:2076","\:2077","\:2078","\:2079"}[[ind+1]];

InterpretInfinitesimalFucntion[InfVar_]:=Block[{Str,Var,DepStr,Dep},
	Str = ToString[InfVar];
	{Var,DepStr} = StringSplit[Str,"["];
	Var = ToExpression[Var];
	Dep = ToExpression/@StringSplit[StringDelete[DepStr,"]"],","];
	{Var,Dep}
]



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
Xstring = StringJoin[Riffle[Table["x"<>SuperscriptNumber[i],{i,0,\[DoubleStruckCapitalD]-1}],","]];

Notation[ParsedBoxWrapper[RowBox[{SubscriptBox["\[PartialD]", "n_"], "Func_"}]] \[DoubleLongRightArrow] ParsedBoxWrapper[RowBox[{"Simplify", "[", RowBox[{"D", "[", RowBox[{"Func_", ",", RowBox[{"\[DoubleStruckX]", "[", "n_", "]"}]}], "]"}], "]"}]]];
Notation[ParsedBoxWrapper[RowBox[{SubscriptBox["\[PartialD]", "n_"], RowBox[{"[", "Func_", "]"}]}]] \[DoubleLongRightArrow] ParsedBoxWrapper[RowBox[{"Simplify", "[", RowBox[{"D", "[", RowBox[{"Func_", ",", RowBox[{"\[DoubleStruckX]", "[", "n_", "]"}]}], "]"}], "]"}]]];
Notation[ParsedBoxWrapper[SuperscriptBox["x", "i_"]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"\[DoubleStruckX]", "[", "i_", "]"}]]];

CheckCoordinates  = True;
Protect[\[DoubleStruckCapitalX],x,CheckCoordinates];
];

ErrorCoordinatesMessage := If[!CheckCoordinates,Print["Error. You must define coordinates first."]];




(* ::Subsection:: *)
(*Define Metric*)


InfVar = h[r,t]
\[DoubleStruckCapitalX]

InterpretInfinitesimalFucntion[h[r,t]]


Unprotect[g,MetricCovM,MetricDet,MetricCon,CheckMetric];
ClearAll[g,MetricCovM,MetricDet,MetricCon,CheckMetric];
CheckMetric  = False;

Options[DefineMetric] = {BackgroundMetric -> MinkCov, PerturbationLabel -> h,PerturbationDependencies -> {}}

DefineMetric[OptionsPattern[]] := Block[{},
	ErrorCoordinatesMessage;
	If[CheckCoordinates,
		Unprotect[MinkCov,MinkCon,n,g,MetricCovM,MetricDet,MetricConM,CheckMetric];
		ClearAll[MinkCov,MinkCon,n,g,MetricCovM,MetricDet,MetricConM,CheckMetric];

		MinkCov = OptionValue[BackgroundMetric];
		MinkCon = Inverse[MinkCov]
		
		Notation[ParsedBoxWrapper[SubscriptBox["\[Eta]", GridBox[{{"i_", "j_"}}]]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{RowBox[{"MinkCov", "[", RowBox[{"[", RowBox[{"i_", "+", "1"}], "]"}], "]"}], "[", RowBox[{"[", RowBox[{"j_", "+", "1"}], "]"}], "]"}]]];
		Notation[ParsedBoxWrapper[SuperscriptBox["\[Eta]", GridBox[{{"i_", "j_"}}]]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{RowBox[{"MinkCon", "[", RowBox[{"[", RowBox[{"i_", "+", "1"}], "]"}], "]"}], "[", RowBox[{"[", RowBox[{"j_", "+", "1"}], "]"}], "]"}]]];
		
		CheckMetric = True;
		Protect[MinkCov,MinkCon,n,g,MetricCovM,MetricDet,MetricConM,CheckMetric];
	];
];

ErrorMetricMessage := If[!CheckMetric,Print["Error. You must define the metric first."]];
