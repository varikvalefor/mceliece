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

\chapter{la'oi .\D MCParam.\ je zo'e}

\section{la'oi .\D MCParam.}
ni'o ro da poi me'oi .\D MCParam.\ zo'u da sinxa lo me'oi .parameter.\ be lo mu'oi glibau.\ Classic MCELIECE .glibau.\ co'e

\subsection{le me'oi .field.}

ni'o la'o zoi.\ \F{MCParam.n} \D q .zoi.\ ni lo me'oi .code.\ pe \D q cu clani

ni'o la'o zoi.\ \F{MCParam.m} \D q .zoi.\ ni 
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
    ν : ℕ
    μ : Fin ν
\end{code}

\section{la'oi .\F k.}
ni'o la'o zoi.\ \F k \B x .zoi.\ me'oi .dimension.\ lo se sinxa be la'oi .\B x.

\begin{code}
k : MCParam → ℕ
k x = (toℕ $ MCParam.n x) ∸ MCParam.m x * (MCParam.t x)
\end{code}
\end{document}
