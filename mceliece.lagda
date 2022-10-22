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

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\title{le me'oi .Agda.\ me'oi .implementation.\ be la'o zoi.\ Classic MCELIECE .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}

\maketitle

\chapter{le me'oi .disclaimer.}
ni'o le proga cu na xamgu je cu na mulno

\chapter{le me'oi .preamble.}
\begin{code}
open import Data.Fin
open import Data.Nat
open import Data.Vec
open import Function
open import Data.Bool
open import Data.Nat.Primality
open import Algebra.Solver.Ring
open import Relation.Nullary.Decidable using (from-yes)
\end{code}

\begin{code}
postulate fromℕ! : ∀ {o : ℕ} → (n : ℕ) → (n Data.Nat.< o) → Fin o
\end{code}

\chapter{la'oi .\D{Chevy}.\ je zo'e}

\section{la'oi .\D{Chevy}.}
ni'o la'o zoi.\ \D{Chevy} \B n .zoi.\ cu sinxa lo mu'oi glibau.\ GALOIS field .glibau.\ poi se me'oi .order.\ la'oi .\B n.

ni'o ko'a goi zo'oi .\D{𝔽Ord}.\ pamoi cmene  .i ku'i ko'a na mutce lo ka ce'u zdile la .varik.

\begin{code}
postulate Chevy : (n : ℕ) → Prime n → Set
\end{code}

\section{la'o zoi.\ \F{\_+Ch\_} .zoi.}
ni'o la'o zoi.\ \B a \Sym{+Ch} \B b .zoi.\ sumji la'oi .\B a.\ la'oi .\B b.

\begin{code}
postulate _+Ch_ : {a b : ℕ} → {c : Prime a} → {d : Prime b}
                → Chevy a c → Chevy b d → Set
\end{code}

\section{la'o zoi.\ \F{\_-Ch\_} .zoi.}
ni'o la'o zoi.\ \B a \Sym{-Ch} \B b .zoi.\ vujnu la'oi .\B a.\ la'oi .\B b.

\begin{code}
postulate _-Ch_ : {a b : ℕ} → {c : Prime a} → {d : Prime b}
                → Chevy a c → Chevy b d → Set
\end{code}

\section{la'o zoi.\ \F{\_*Ch\_} .zoi.}
ni'o la'o zoi.\ \B a \Sym{*Ch} \B b .zoi.\ pilji la'oi .\B a.\ la'oi .\B b.

\begin{code}
postulate _*Ch_ : {a b : ℕ} → {c : Prime a} → {d : Prime b}
                → Chevy a c → Chevy b d → Set
\end{code}

\section{la'o zoi.\ \F{\_/Ch\_} .zoi.}
ni'o la'o zoi.\ \B a \Sym{/Ch} \B b .zoi.\ dilcu la'oi .\B a.\ la'oi .\B b.

\begin{code}
postulate _/Ch_ : {a b : ℕ} → {c : Prime a} → {d : Prime b}
                → Chevy a c → Chevy b d → Set
\end{code}

\chapter{la'oi .\D{MCParam}.\ je zo'e}

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
ni'o la'o zoi.\ \F {MCParam.k} \B q .zoi.\ me'oi .dimension.\ lo me'oi .code.\ pe la'oi .\B q.

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
    n : Fin (2 ^ m)
    t : ℕ
    -- ^ .i dukse le ka ce'u sampu je nai me'oi .strict.
    -- .i sarcu fa lo nu ko'a goi la'o zoi. MCParam.t x
    -- .zoi. zmadu li re ke je lo nu lo pilji be ko'a bei
    -- la'o zoi. MCParam.m x .zoi. cu mleca la'o zoi.
    -- MCParam.n x .zoi.
    f : (z : ℕ) → {q : Prime z} → Chevy z q
    F : (z : ℕ) → {q : Prime z} → Chevy z q
    ν : ℕ
    μ : Fin ν
    -- ni'o le me'oi .field. poi srana le mu'oi glibau.
    -- symmetric cryptography .glibau. cu cnita dei
    ℓ : ℕ
    H : ℕ → Fin $ 2 ^ ℓ
    σ₁ : ℕ
    -- ^ ni'o dukse le ka ce'u sampu  .i cadga fa lo nu
    -- dubjavmau la'oi .m.
    σ₂ : ℕ
    -- ^ ni'o dukse le ka ce'u sampu  .i cadga fa lo nu
    -- dubjavmau lo pilji be li re bei la'oi .m.
    G : Fin $ 2 ^ ℓ
      → Fin (2 ^ (toℕ n Data.Nat.+
                  σ₂ * (2 ^ m) Data.Nat.+
                  σ₁ * t Data.Nat.+
                  ℓ
      ))
    -- ^`ni'o la .varik. cu jinvi le du'u tolmle... kei
    -- je cu te selneimau lo su'u na pilno lo mu'oi
    -- glibau. line break .glibau.
  k : MCParam → ℕ
  k x = toℕ n  ∸ m * t
\end{code}

\section{la'oi .\D{polly}.}
ni'o la'o zoi.\ \D{polly} x .zoi.\ vasru lo ro me'oi .polynomial.\ pe la'oi .\B x.

\begin{code}
postulate polly : MCParam → Set
\end{code}

\chapter{la'oi .\D{Private}.\ je zo'e}

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
    g : polly p
    Γ : Vec (polly p) $ toℕ (MCParam.n p) Data.Nat.+ 1
    s : Vec Bool $ toℕ $ MCParam.n p
\end{code}
\end{document}
