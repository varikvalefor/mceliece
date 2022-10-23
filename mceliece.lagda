\documentclass{report}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

% \setmathfont{XITS Math}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{∄}{\ensuremath{\mathnormal\nexists}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{∨}{\ensuremath{\mathnormal\vee}}
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{∶}{\ensuremath{\mathnormal\colon\!\!}}
\newunicodechar{⊹}{\ensuremath{\mathnormal\dag}}
\newunicodechar{𝕗}{\ensuremath{\mathbb{f}}}
\newunicodechar{ℙ}{\ensuremath{\mathbb{P}}}
\newunicodechar{𝔽}{\ensuremath{\mathbb{F}}}
\newunicodechar{𝕄}{\ensuremath{\mathbb{M}}}
\newunicodechar{ν}{\ensuremath{\nu}}
\newunicodechar{μ}{\ensuremath{\mu}}
\newunicodechar{◆}{\ensuremath{\mathnormal\blackdiamond}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{^\mathrm{b}}}
\newunicodechar{≥}{\ensuremath{\mathnormal{\geq}}}
\newunicodechar{ϕ}{\ensuremath{\mathnormal{\phi}}}
\newunicodechar{χ}{\ensuremath{\mathnormal{\chi}}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\wedge}}}
\newunicodechar{∅}{\ensuremath{\mathnormal{\emptyset}}}
\newunicodechar{∣}{\ensuremath{\mathnormal{|}}}
\newunicodechar{⁇}{\ensuremath{\mathrm{?\!?}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\forall}}
\newunicodechar{ℓ}{\ensuremath{\ell}}
\newunicodechar{σ}{\ensuremath{\sigma}}
\newunicodechar{₁}{\ensuremath{_1}}
\newunicodechar{₂}{\ensuremath{_2}}
\newunicodechar{≤}{\ensuremath{\mathnormal{\leq}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\title{le me'oi .Agda.\ me'oi .implementation.\ be la'o glibau.\ Classic MCELIECE .glibau.}
\author{la .varik.\ .VALefor.}

\begin{document}

\maketitle

\tableofcontents

\chapter{le me'oi .disclaimer.}
ni'o le proga cu na xamgu je cu na mulno

\chapter{le me'oi .preamble.}
ni'o la'au le me'oi .preamble.\ li'u vasru le .importe ja me'oi .pragma.\ selsku

\begin{code}
open import Data.Fin
  renaming (
    _+_ to _+F_
  )
open import Data.Nat
open import Data.Vec
open import Function
open import Data.Bool
  hiding (
    T
  )
open import Data.Nat.DivMod
open import Data.Nat.Primality
open import Algebra.Solver.Ring
open import Relation.Nullary.Decidable using (from-yes)
\end{code}

\chapter{le vrici}
ni'o la'au le vrici li'u vasru zo'e poi ke'a goi ko'a zo'u na racli fa lo nu zbasu lo me'oi .chapter.\ poi vasru ko'a po'o

\section{la'oi .\F{\_div2\_}.}
ni'o gonai ge la'oi .\B b.\ du li no gi ko'a goi la'o zoi.\ \B a \Sym{div2} b .zoi.\ du li no gi ko'a dilcu la'oi .\B a.\ la'oi .\B b.

\begin{code}
_div2_ : ℕ → ℕ → ℕ
_ div2 0 = 0
a div2 (suc b) = a div (suc b)
\end{code}

\chapter{la'oi .\D 𝕄.\ je zo'e}
ni'o la'au la'oi .\D M.\ je zo'e li'u vasru le velcki be ko'a goi la'oi .\D M.\ je le pinka be ko'a be'o je ko'a goi le fancu poi srana la'oi .\D M.\ po'o ku'o je le pinka be ko'a

\section{la'oi .\D 𝕄.}
ni'o ro da poi mu'oi zoi.\ .\D 𝕄 \B a \B b .zoi.\ zo'u da nacmeimei la'oi .\B a.\ la'oi .\B b.

\begin{code}
postulate 𝕄 : ∀ {a} → (A : Set a) → ℕ → ℕ → Set
\end{code}

\chapter{la'oi .\D{MCParam}.\ je zo'e}
ni'o la'au la'oi .\D MCParam.\ je zo'e li'u vasru le velcki be ko'a goi la'oi .\D MCParam.\ je le pinka be ko'a be'o je ko'a goi le fancu poi srana la'oi .\D MCParam.\ po'o ku'o je le pinka be ko'a

\section{la'oi .\D{MCParam}.}
ni'o ro da poi me'oi .\D{MCParam}.\ zo'u da sinxa lo me'oi .parameter.\ be lo mu'oi glibau.\ Classic MCELIECE .glibau.\ co'e

\subsection{le me'oi .field.}

\subsubsection{le vrici je me'oi .field.}
\paragraph{la'oi .\F{MCParam.n}.}
ni'o la'o zoi.\ \F{MCParam.n} \D q .zoi.\ ni lo me'oi .code.\ pe \D q cu clani

\paragraph{la'oi .\F{MCParam.m}.}
ni'o la'o zoi.\ \F{MCParam.m} \D q .zoi.\ dugri lo ni lo me'oi .field.\ cu barda kei li re

\paragraph{la'oi .\F{MCParam.t}.}
ni'o la'o zoi.\ \F{MCParam.t} \D q .zoi.\ ni me'oi .guarantee.\ le du'u cumki fa lo nu rinka ja gasnu ja zo'e lo nu binxo lo drani

\paragraph{la'oi .\F{MCParam.f}.}
ni'o la'o zoi.\ \F{MCParam.f} \B q .zoi.\ me'oi .monic.\ je me'oi .irreducible.\ cpolynomi'a be fi la'o zoi.\ \F{MCParam.m} \B q .zoi\ldots je cu co'e

\paragraph{la'oi .\F{MCParam.F}.}
ni'o la'o zoi.\ \F{MCParam.F} \B q .zoi.\ me'oi .monic.\ je me'oi .irreducible.\ cpolynomi'a be fi la'o zoi.\ \F{MCParam.t} \B q .zoi\ldots je cu co'e

\paragraph{la'oi .\F{MCParam.k}.}
ni'o la'o zoi.\ \F{MCParam.k} \B q .zoi.\ me'oi .dimension.\ lo me'oi .code.\ pe la'oi .\B q.

\paragraph{la'oi .\F{MCParam.ν}.}
ni'o la'o zoi.\ \F{MCParam.ν} \B q .zoi.\ dubjavmau li no je cu dubjavme'a lo sumji be la'o zoi.\ \F{MCParam.k} \B q .zoi.\ bei la'o zoi.\ \F{MCParam.μ \B q} .zoi.

\paragraph{la'oi .\F{MCParam.ν}.}
ni'o la'o zoi.\ \F{MCParam.μ} \B q .zoi.\ dubjavmau li no je cu dubjavme'a la'o zoi.\ \F{MCParam.ν \B q} .zoi.\ je cu dubjavme'a lo vujnu be la'o zoi.\ \F{MCParam.ν} \B q .zoi.\ bei la'o zoi.\ \F{MCParam.k} \B q .zoi.

\subsubsection{le me'oi .field.\ poi srana le mu'oi glibau.\ symmetric cryptography .glibau.}
\paragraph{la'oi .\F{MCParam.ℓ}.}
ni'o la'o zoi.\ \F{MCParam.ℓ} \B q .zoi.\ ni clani fa lo me'oi .output.\ be la'o zoi.\ \F{MCParam.H} \B q .zoi.\

\paragraph{la'oi .\F{MCParam.H}.}
ni'o la'o zoi.\ \F{MCParam.H} \B q .zoi.\ me'oi .hash.\ fancu

\paragraph{la'oi .\F{MCParam.σ₁}.}
ni'o la'o zoi.\ \F{MCParam.σ₁} \B q .zoi.\ me'oi .arbitrary.

\paragraph{la'oi .\F{MCParam.σ₂}.}
.i la'o zoi.\ \F{MCParam.σ₂} \B q .zoi.\ go'i

\paragraph{la'oi .\F{MCParam.G}.}
ni'o la'o zoi.\ \F{MCParam.G} \B q \B x .zoi.\ cu me'oi .pseudorandom.\ poi ke'a goi ko'a zo'u pilno la'oi .\B x.\ lo nu me'oi .calculate.\ ko'a

\begin{code}
record MCParam : Set
  where
  field
    m : ℕ
    n : Fin $ suc $ 2 ^ m
    t : Fin $ (toℕ n) div2 m
    -- ^ ni'o dukse le ka ce'u sampu je nai me'oi .strict.
    -- .i sarcu fa lo nu la'o zoi. MCParam.t x .zoi.
    -- dubjavmau li re
  q : ℕ
  q = 2 ^ m
  -- | ni'o le su'u dargau cu tolmle la .varik.  .i ku'i
  -- ganai co'e le me'oi .alternative. gi lo me'oi .hbox.
  -- cu me'oi .overfull.  .i mabla
  field
    f : Vec (Fin 2) m
    F : Vec (Fin q) $ toℕ t
    ν : ℕ
    -- ^ ni'o dukse le ka ce'u sampu  .i sarcu fa lo nu
    -- dubjavme'a lo sumji be la'oi .μ. bei la'oi .k.
    μ : Fin $ ν + 1
    -- ni'o le me'oi .field. poi srana le mu'oi glibau.
    -- symmetric cryptography .glibau. cu cnita dei
    ℓ : ℕ
    H : ℕ → Fin $ 2 ^ ℓ
    σ₁ : ℕ
    -- ^ ni'o dukse le ka ce'u sampu  .i sarcu fa lo nu
    -- dubjavmau la'oi .m.
    σ₂ : ℕ
    -- ^ ni'o dukse le ka ce'u sampu  .i cadga fa lo nu
    -- dubjavmau lo pilji be li re bei la'oi .m.
    G : Fin $ 2 ^ ℓ → Fin $ 2 ^ (toℕ n + σ₂ * q + σ₁ * toℕ t + ℓ)
  k : ℕ
  k = toℕ n ∸ m * toℕ t
\end{code}

\chapter{la'oi .\D{Private}.\ je zo'e}
ni'o la'au la'oi .\D Private.\ je zo'e li'u vasru le velcki be ko'a goi la'oi .\D Private.\ je le pinka be ko'a be'o je ko'a goi le fancu poi srana la'oi .\D Private.\ po'o ku'o je le pinka be ko'a

\section{la'oi .\D{Private}.}
ni'o ro da poi me'oi .\D{Private}.\ zo'u da sinxa lo sivni termifckiku pe la'o glibau.\ Classic MCELIECE .glibau.

\subsection{le me'oi .field.}

\paragraph{la'oi .\F{Private.g}.}
ni'o la'o zoi.\ \F{Private.g} \B p .zoi.\ cpolinomi'a

\paragraph{la'oi .\F{Private.Γ}.}
ni'o la'o zoi.\ \F{Private.Γ} \B p) .zoi.\ liste lo'i cpolinomi'a je cu se nilzilcmi lo sumji be la'o zoi.\ \F{toℕ} \Sym\$ \F{MCParam.n} \B p .zoi.\ bei li pa

\paragraph{la'oi .\F{Private.s}.}
ni'o la'o zoi.\ \F{Private.s} \B p .zoi.\ liste lo'i samsle je cu se nilzilcmi la'o zoi.\ \F{toℕ} \Sym\$ \F{MCParam.n} \B p .zoi.

\begin{code}
record Private (p : MCParam) : Set
  where
  field
    g : {n : ℕ} → Vec (Fin $ MCParam.q p) n
    Γ : Vec (Fin $ MCParam.q p) $ suc $ toℕ $ MCParam.n p
    s : Vec (Fin 2) $ toℕ $ MCParam.n p
\end{code}

\chapter{la'oi .\D{Public}.}
ni'o la'au la'oi .\D{Public}.\ je zo'e li'u vasru le velcki be ko'a goi la'oi .\D{Public}.\ je le pinka be ko'a be'o je ko'a goi le fancu poi srana la'oi .\D{Public}.\ po'o ku'o je le pinka be ko'a

\section{la'oi .\D{Public}.}
ni'o ro da poi me'oi .\D{Public}.\ zo'u da sinxa lo gubni termifckiku

\subsection{le me'oi .field.}

\paragraph{la'oi .\F{T}.}
ni'o la'o zoi.\ \F{Public.T} \B q .zoi.\ nacmeimei lo vujnu be la'o zoi.\ \F{fromℕ} \Sym\$ \F{MCParam.n} \B q .zoi.\ bei la'o zoi.\ \F{MCParam.k} \B p .zoi.\ je cu vasru lo cmima be la'o zoi.\ \D{Fin} 2 .zoi.\ po'o

\begin{code}
record Public (p : MCParam) : Set
  where
  field
    T : 𝕄 (Fin 2) (toℕ (MCParam.n p) ∸ MCParam.k p) $ MCParam.k p
\end{code}
\end{document}
