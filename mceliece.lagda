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

\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{∶}{\ensuremath{\mathnormal\colon\!\!}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb F}}}
\newunicodechar{𝕄}{\ensuremath{\mathnormal{\mathbb M}}}
\newunicodechar{𝕊}{\ensuremath{\mathnormal{\mathbb S}}}
\newunicodechar{𝕃}{\ensuremath{\mathnormal{\mathbb L}}}
\newunicodechar{𝔹}{\ensuremath{\mathnormal{\mathbb B}}}
\newunicodechar{ν}{\ensuremath{\mathnormal\nu}}
\newunicodechar{μ}{\ensuremath{\mathnormal\mu}}
\newunicodechar{τ}{\ensuremath{\mathnormal\tau}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{ˡ}{\ensuremath{\mathnormal{^\AgdaFontStyle{l}}}}
\newunicodechar{ʳ}{\ensuremath{\mathnormal{^\AgdaFontStyle{r}}}}
\newunicodechar{≥}{\ensuremath{\mathnormal\geq}}
\newunicodechar{≮}{\ensuremath{\mathnormal\nless}}
\newunicodechar{ϕ}{\ensuremath{\mathnormal\phi}}
\newunicodechar{∧}{\ensuremath{\mathnormal\wedge}}
\newunicodechar{∣}{\ensuremath{\mathnormal |}}
\newunicodechar{∘}{\ensuremath{\mathnormal\circ}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal\ell}}
\newunicodechar{σ}{\ensuremath{\mathnormal\sigma}}
\newunicodechar{π}{\ensuremath{\mathnormal\pi}}
\newunicodechar{α}{\ensuremath{\mathnormal\alpha}}
\newunicodechar{₀}{\ensuremath{\mathnormal{_0}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_\AgdaFontStyle{i}}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_\AgdaFontStyle{l}}}}
\newunicodechar{ₓ}{\ensuremath{\mathnormal{_\AgdaFontStyle{x}}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_\AgdaFontStyle{v}}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_\AgdaFontStyle{m}}}}
\newunicodechar{ₚ}{\ensuremath{\mathnormal{_\AgdaFontStyle{p}}}}
\newunicodechar{≤}{\ensuremath{\mathnormal\leq}}
\newunicodechar{⍉}{\ensuremath{\mathnormal{∘\hspace{-0.455em}\backslash}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{δ}{\ensuremath{\mathnormal\delta}}
\newunicodechar{⇒}{\ensuremath{\mathnormal\Rightarrow}}
\newunicodechar{⇐}{\ensuremath{\mathnormal\Leftarrow}}
\newunicodechar{↔}{\ensuremath{\mathnormal\leftrightarrow}}
\newunicodechar{≰}{\ensuremath{\mathnormal\nleq}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\hspace{-0.3em}|}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{|\hspace{-0.3em}\rbrace}}}
\newunicodechar{▹}{\ensuremath{\mathnormal\triangleright}}
\newunicodechar{⊓}{\ensuremath{\mathnormal\sqcap}}
\newunicodechar{⊎}{\ensuremath{\mathnormal\uplus}}
\newunicodechar{⍨}{\raisebox{-0.25ex}{$\ddot\sim$}}

% | ni'o tu'a le canlu lerfu cu milxe le ka ce'u fegli kei je ku'i cu mutce le ka ce'u filri'a lo nu na me'oi .overfull.
%
% ni'o le smimlu cu krinu le su'u la .varik. cu nelci le su'u so'i da poi ke'a jufra fi la .lojban. zo'u cmalu je cmavo fa lo so'e valsi pe da
\newcommand\hashish{cbf1 42fe 1ebd b0b2 87a4 4018 340b 8159 7ef1 3a63 6f5d 76f4 6f48 a080 b2bc d3f1 3922 f0f1 5219 94cc 5e71 fb1f b2d9 d9f8 dd3b ffe6 be32 0056 5cca 21c4 28eb 9de1}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\newcommand\sds{\spacefactor\sfcode`.\ \space}

\newcommand\algoritma\textsc

\newcommand\xactaipes[1]{\textsc{#1}}

\newcommand\specimp[1]{ni'o la'oi .\F{#1}.\ velcki ja co'e ko'a goi la'oi .\algoritma{#1}.\ poi ke'a se velcki le selvau be la'o cmene.\ mceliece-20201010.pdf .cmene.\ poi ke'a xi re se me'oi .SHA512.\ zoi zoi.\ \hashish\ .zoi.}

% | ni'o so'i da poi ke'a ckupau zo'u lo broda cei me'oi .abstract. be da cu vasru lo cmene be da  .i ko'a goi tu'a la'oi .chapsname. je la'oi .chap. cu rinka lo nu na sarcu fa lo nu broda batkyci'a lo cmene be lo ckupau
%
% .i ko'a na mutce le ka ce'u melbi la .varik... kei ja le ka ce'u fegli la .varik.
% .i la .varik. cu curmi lo nu stidi
\newcommand\chapsname{}
\newcommand\chap[1]{
	\renewcommand\chapsname{#1}
	\chapter{#1}
}

\newcommand\termineidyr[1]{ga naja la .varik.\ cu djuno lo du'u ma kau ctaipe lo su'u la'o zoi.\ \F{#1}\ .zoi.\ kanji se fanmo fancu gi lakne fa lo nu la .varik.\ cu co'e ja cu basygau zo'oi .TERMINATING.\ zoi glibau.\ NON\_TERMINATING .glibau.}

\title{le me'oi .Agda.\ velcki be la'o glibau.\ Classic MCELIECE .glibau.}
\author{la .varik.\ .VALefor.}

\begin{document}

\maketitle

\tableofcontents

\chap{le me'oi .disclaimer.}
ni'o le velcki cu zabna najenai cu mulno

\chap{le terzu'e}
ni'o me'oi .Agda,\ co'e fa ko'a goi la'au le me'oi .Agda.\ velcki be la'o glibau.\ Classic MCELIECE .glibau.\ li'u\sds  .i tu'a ko'a filri'a lo nu jimpe fi la'o glibau.\ Classic MCELIECE .glibau.

.i la .varik.\ cu mutce le ka ce'u troci lo nu ko'a drani je cu zabna fi vo'a\ldots kei kei je nai le ka ce'u troci lo nu ko'a mutce le ka ce'u xi re skami sutra co'e\sds  .i ku'i la .varik.\ na toldji lo da'i nu ko'a drani ba'e je cu skami sutra co'e

\chap{le me'oi .preamble.}
ni'o la'au \chapsname\ li'u vasru le .importe ja me'oi .pragma.\ selsku

\begin{code}
{-# OPTIONS --guardedness #-}

open import IO
  using (
    _<$>_;
    pure;
    IO
  )
open import Data.Fin
  as 𝔽
  using (
    opposite;
    fromℕ<;
    fromℕ;
    zero;
    toℕ;
    Fin;
    suc
  )
open import Data.Sum
  as _⊎_
  using (
    _⊎_
  )
open import Data.Vec
  using (
    replicate;
    fromList;
    allFin;
    filter;
    lookup;
    toList;
    unzip;
    drop;
    take;
    _∷_;
    Vec;
    []
  )
  renaming (
    zipWith to zipWithᵥ;
    reverse to reverseᵥ;
    foldr to foldrᵥ;
    map to mapᵥ;
    sum to sumᵥ;
    zip to zipᵥ
  )
open import Function
  using (
    const;
    _∘₂_;
    _on_;
    flip;
    _∋_;
    _$_;
    _∘_;
    id
  )
  renaming (
    -- | ni'o smimlu ko'a goi le .asycy'i'is. co'e...
    -- je ku'i cu mleca ko'a le ka ce'u fegli la .varik.
    _|>_ to _▹_
  )
open import Data.Bool
  using (
    if_then_else_;
    false;
    Bool;
    true
  )
open import Data.List
  as 𝕃
  using (
    reverse;
    List;
    _∷_;
    []
  )
  renaming (
    map to mapₗ
  )
open import Data.Digit
  using (
    toDigits
  )
open import Data.Maybe
  using (
    decToMaybe;
    fromMaybe;
    nothing;
    maybe′;
    Maybe;
    maybe;
    just
  )
  renaming (
    _>>=_ to _>>=ₘ_;
    map to mapₘ;
    ap to apₘ
  )
open import Data.These
  using (
    These;
    these;
    this;
    that
  )
open import Data.String
  as 𝕊
  using (
    String
  )
open import Algebra.Core
  using (
    Op₁;
    Op₂
  )
open import Data.Product
  using (
    uncurry;
    proj₁;
    proj₂;
    <_,_>;
    map₂;
    _×_;
    _,_;
    Σ;
    ∃
  )
open import Data.Nat
  as ℕ
  using (
    _^_;
    _*_;
    _+_;
    _∸_;
    suc;
    ℕ
  )
open import Relation.Unary
  using (
    Decidable;
    _⊆_
  )
open import Data.Nat.DivMod
  using (
    _div_
  )
open import Relation.Nullary
  using (
    Dec;
    yes;
    no;
    ¬_
  )
open import Data.Nat.Properties
  as DNP
  using (
  )
  renaming (
    ≤-irrelevant to ≤≡≤
  )
open import Truthbrary.Data.Fin
  using (
    tomindus;
    mink
  )
open import Truthbrary.Record.Eq
  using (
    _≡ᵇ_;
    _≟_;
    Eq
  )
open import Truthbrary.Record.SR
  using (
    show
  )
open import Truthbrary.Record.LLC
  using (
    nu,iork;
    length;
    _++_;
    _∈_;
    map;
    vec;
    LL
  )
open import Relation.Nullary.Negation
  renaming (
    contradiction to _⇒⇐_
  )
open import Relation.Nullary.Decidable
  using (
    dec-no;
    isYes
  )
open import Truthbrary.Data.Vec.Matrix
  using (
    _∣_;
    I;
    𝕄
  )
open import Relation.Binary.PropositionalEquality
  using (
    module ≡-Reasoning;
    subst;
    cong;
    refl;
    _≗_;
    _≡_;
    sym
  )

import Agda.Builtin.IO as ABIO
import Data.Fin.Properties as DFP
import Data.Vec.Properties as DVP
import Data.List.Properties as DLP
import Data.Maybe.Properties as DMP
import Data.Product.Properties as DPP
import Data.List.Relation.Unary.All as Listal
\end{code}

\chap{le vrici}
ni'o la'au \chapsname\ li'u vasru zo'e poi na racli fa lo nu zbasu lo ckupau poi srana ke'a xi pa fa lo ro selvau be ke'a xi re

\section{la'o zoi.\ \F{dun?}\ .zoi.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu vo'a ciksi la'o zoi.\ \F{dun?}\ .zoi.\ bau la .lojban.

\begin{code}
dun? : ∀ {a} → {A : Set a} → {B C : A}
     → ⦃ Eq A ⦄
     → Maybe $ B ≡ C
dun? = decToMaybe $ _ ≟ _
\end{code}

\subsection{le ctaipe be le su'u la'o zoi.\ \F{dun?}\ .zoi.\ mapti}

\begin{code}
module Dun?Veritas where
  jus : ∀ {a} → {A : Set a}
      → ⦃ _ : Eq A ⦄
      → {x z : A}
      → (d : x ≡ z)
      → dun? ≡ just d
  jus {x = x} {z} d = begin
    dun? ≡⟨ refl ⟩
    decToMaybe (x ≟ z) ≡⟨ DY ▹ proj₂ ▹ cong decToMaybe ⟩
    decToMaybe (yes $ proj₁ DY) ≡⟨ refl ⟩
    _ ≡⟨ ≡≡≡ (proj₁ DY) d ▹ cong (decToMaybe ∘ yes) ⟩
    decToMaybe (yes d) ≡⟨ refl ⟩
    just d ∎
    where
    open ≡-Reasoning
    DY = Relation.Nullary.Decidable.dec-yes (x ≟ z) d
    ≡≡≡ : (d₁ d₂ : x ≡ z) → d₁ ≡ d₂
    ≡≡≡ refl refl = refl
\end{code}

\section{la'oi .\F{hWV𝔽}.}
ni'o ko'a goi la'o zoi.\ \F{hWV𝔽} \B x\ .zoi.\ mu'oi glibau.\ HAMMING weight .glibau.\ la'oi .\B x.\sds  .i sa'u nai ko'a nilzilcmi lo'i ro co'e poi la'oi .\AgdaInductiveConstructor{zero}.\ na meirmoi ke'a fo la'oi .\B x.

\begin{code}
hWV𝔽 : {a b : ℕ} → Vec (Fin b) a → ℕ
hWV𝔽 = sumᵥ ∘ mapᵥ (λ {(suc _) → 1; zero → 0})
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{hWV𝔽}.\ mapti}

\begin{code}
module HWV𝔽Veritas where
  kunti : {a : ℕ} → hWV𝔽 ([] {A = Fin a}) ≡ 0
  kunti = refl

  dunlis : {a b : ℕ}
         → (x : Vec (Fin $ suc b) a)
         → hWV𝔽 (zero ∷ x) ≡ hWV𝔽 x
  dunlis _ = refl

  cykas : {a b : ℕ}
        → (x : Vec (Fin $ suc b) a)
        → (z : Fin _)
        → hWV𝔽 (suc z ∷ x) ≡ suc (hWV𝔽 x)
  cykas _ _ = refl

  dubjavme'a : {a b : ℕ}
             → (x : Vec (Fin $ suc a) b)
             → hWV𝔽 x ℕ.≤ b
  dubjavme'a [] = ℕ.z≤n
  dubjavme'a (zero ∷ x) = DNP.≤-trans (dubjavme'a x) $ DNP.n≤1+n _
  dubjavme'a (suc _ ∷ xs) = dubjavme'a xs ▹ ℕ.s≤s
\end{code}

\section{la'oi .\F{f2f}.}
ni'o ga naja la'oi .\B a.\ ctaipe la'o zoi.\ \D{Fin} \B m\ .zoi.\ gi ga jonai ko'a goi la'o zoi.\ \F{toℕ}\ \B a\ .zoi.\ du ko'e goi la'o zoi.\ \F{toℕ} \OpF \$ \F{f2f} \Sym\{\B n\Sym\} \Sym\{\B n\Sym\} \B a\ .zoi.\ gi ga je ko'a dubjavmau la'oi .\B m.\ gi ko'e du la'oi .\B n.

\begin{code}
module F2f where
  _<?ₘ_ : (m n : ℕ) → Maybe $ m ℕ.< n
  _<?ₘ_ = decToMaybe ∘₂ ℕ._<?_

  mFdᵢ : {m n : ℕ} → Maybe $ n ℕ.< suc m → Fin $ suc m
  mFdᵢ {m} = maybe′ fromℕ< $ fromℕ< $ DNP.n<1+n m

  mFd : {m : ℕ} → ℕ → Fin $ suc m
  mFd = mFdᵢ ∘ (_<?ₘ _)

  f2f : {m n : ℕ} → Fin m → Fin $ suc n
  f2f = mFd ∘ toℕ

open F2f
  using (
    f2f
  )
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{f2f}.\ mapti}

\begin{code}
module F2fVeritas where
  open ≡-Reasoning
  open F2f

  module _<?ₘ_ where
    go'is : {m n : ℕ}
          → (x : m ℕ.< n)
          → m <?ₘ n ≡ just x
    go'is {m} {n} x = begin
      m <?ₘ n ≡⟨ refl ⟩
      decToMaybe (m ℕ.<? n) ≡⟨ proj₂ DY ▹ cong decToMaybe ⟩
      decToMaybe (yes $ proj₁ DY) ≡⟨ refl ⟩
      just (proj₁ DY) ≡⟨ ≤≡≤ _ _ ▹ cong just ⟩
      just x ∎
      where
      DY = Relation.Nullary.Decidable.dec-yes (m ℕ.<? _) x

    nago'is : {m n : ℕ} → ¬_ $ m ℕ.< n → m <?ₘ n ≡ nothing
    nago'is J = DN _ J ▹ proj₂ ▹ cong decToMaybe
      where
      DN = Relation.Nullary.Decidable.dec-no

  module MFdᵢ where
    jus : {m n : ℕ}
        → (j : m ℕ.< suc n)
        → m ≡_ $ toℕ $ mFdᵢ $ just j
    jus = sym ∘ DFP.toℕ-fromℕ<

    nada : {m n : ℕ} → n ≡_ $ toℕ $ mFdᵢ {n} {m} nothing
    nada = DFP.toℕ-fromℕ< _ ▹ sym

    jonais : {m n : ℕ}
           → (j : Maybe _)
           → let t = toℕ $ mFdᵢ {n} {m} j in
             (t ≡ m) ⊎ (n ≡ t)
    jonais {m} = maybe (_⊎_.inj₁ ∘ sym ∘ jus) $ _⊎_.inj₂ $ nada {m}

  module MFd where
    mleca : {m n : ℕ}
          → m ℕ.< suc n
          → m ≡_ $ toℕ $ mFd {n} m
    mleca {m} {n} x = sym $ begin
      toℕ (mFd m) ≡⟨ refl ⟩
      toℕ (mFdᵢ $ m <?ₘ _) ≡⟨ _<?ₘ_.go'is x ▹ cong (toℕ ∘ mFdᵢ) ⟩
      toℕ (mFdᵢ $ just x) ≡⟨ MFdᵢ.jus {m} {n} x ▹ sym ⟩
      m ∎

    dubjavmau : {m n : ℕ}
              → ¬_ $ m ℕ.< suc n
              → n ≡_ $ toℕ $ mFd {n} m
    dubjavmau {m} {n} J = sym $ begin
      toℕ (mFd m) ≡⟨ refl ⟩
      toℕ (mFdᵢ $ m <?ₘ _) ≡⟨ _<?ₘ_.nago'is J ▹ cong (toℕ ∘ mFdᵢ) ⟩
      toℕ (mFdᵢ {n = n} nothing) ≡⟨ MFdᵢ.nada {m} {n} ▹ sym ⟩
      n ∎

  dubjavmau : {m n : ℕ}
            → (f : Fin m)
            → ¬_ $ toℕ f ℕ.< suc n
            → n ≡_ $ toℕ $ f2f {n = n} f
  dubjavmau {n = n} f j = sym $ begin
    toℕ (f2f f) ≡⟨ refl ⟩
    toℕ (mFd $ toℕ f) ≡⟨ MFd.dubjavmau j ▹ sym ⟩
    n ∎

  mleca : {m n : ℕ}
        → (f : Fin m)
        → toℕ f ℕ.< suc n
        → toℕ f ≡_ $ toℕ $ f2f {n = n} f
  mleca {n = n} f m = sym $ begin
    toℕ (f2f f) ≡⟨ refl ⟩
    toℕ (mFd $ toℕ f) ≡⟨ MFd.mleca m ▹ sym ⟩
    toℕ f ∎

  dunli : {m n : ℕ}
        → (f : Fin m)
        → toℕ (f2f {n = n} f) ≡ n ℕ.⊓ toℕ f
  dunli {m} {n} f with toℕ f ℕ.<? suc n
  ... | yes x = begin
    toℕ (mFdᵢ $ just x) ≡⟨ MFdᵢ.jus x ▹ sym ⟩
    toℕ f ≡⟨ DNP.m≥n⇒m⊓n≡n (<⇒≤ x) ▹ sym ⟩
    n ℕ.⊓ toℕ f ∎
    where
    <⇒≤ : {m n : ℕ} → m ℕ.< suc n → m ℕ.≤ n
    <⇒≤ (ℕ.s≤s s) = s
  ... | no x = begin
    toℕ (mFdᵢ {n = m} nothing) ≡⟨ MFdᵢ.nada {m} {n} ▹ sym ⟩
    n ≡⟨ DNP.m≤n⇒m⊓n≡m (≰⇒≤⍨ x) ▹ sym ⟩
    n ℕ.⊓ toℕ f ∎
    where
    ≰⇒≤⍨ : {m n : ℕ}
         → ¬_ $ suc m ℕ.≤ suc n
         → n ℕ.≤ m
    ≰⇒≤⍨ = sykles ∘ ≥⇒≤⍨ ∘ DNP.≮⇒≥
      where
      sykles : {m n : ℕ} → suc m ℕ.≤ n → m ℕ.≤ n
      sykles (ℕ.s≤s s) = DNP.≤-step s
      ≥⇒≤⍨ : {m n : ℕ} → (m ℕ.≥ n) → n ℕ.≤ m
      ≥⇒≤⍨ = id

  zeron : {n m : ℕ}
        → (x : Fin n)
        → toℕ x ≡ 0
        → f2f {n = m} x ≡ zero
  zeron x d = begin
    f2f x ≡⟨ refl ⟩
    mFd (toℕ x) ≡⟨ d ▹ cong mFd ⟩
    mFd 0 ≡⟨ refl ⟩
    zero ∎

  fromℕ-toℕ : {m n : ℕ}
            → (f : Fin m)
            → f2f {n = n} (fromℕ $ toℕ f) ≡ f2f f
  fromℕ-toℕ f = DFP.toℕ-fromℕ (toℕ f) ▹ cong mFd

  fromℕ<-f2f : {m n : ℕ}
             → (f : Fin m)
             → (ml : toℕ f ℕ.< suc n)
             → fromℕ< ml ≡ f2f f
  fromℕ<-f2f {m} {n} zero (ℕ.s≤s ℕ.z≤n) = refl
  fromℕ<-f2f {m} {n} (𝔽.suc f) (ℕ.s≤s s) = sym $ begin
    f2f (𝔽.suc f) ≡⟨ {!!} ⟩
    fromℕ< (ℕ.s≤s s) ∎
\end{code}

\section{la'oi .\F{f𝔽}.}
ni'o ga naja la'oi .\B a.\ ctaipe la'o zoi.\ \D{Fin} \B q\ .zoi.\ gi la'o zoi.\ \F{toℕ} \OpF \$ \F{f𝔽} \B f \B a \B b\ .zoi.\ nacmecrai la'o zoi.\ \F{fromℕ} \OpF \$ \B f \Sym(\F{toℕ} \B a\Sym) \OpF \$ \F{toℕ} \B b\ .zoi.\ ce la'o zoi.\ \B q \OpF{∸} \AgdaNumber 1\ .zoi.

\begin{code}
f𝔽 : {n : ℕ} → Op₂ ℕ → Op₂ $ Fin $ suc n
f𝔽 f = f2f ∘₂ fromℕ ∘₂ f on toℕ
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{f𝔽}.\ mapti}

\begin{code}
module F𝔽Veritas where
  open ≡-Reasoning

  mleca : {n : ℕ}
        → (f : Op₂ ℕ)
        → (x z : Fin $ suc n)
        → (f on toℕ) x z ℕ.< suc n
        → toℕ (f𝔽 f x z) ≡ (f on toℕ) x z
  mleca f x z m = begin
    toℕ (f𝔽 f x z) ≡⟨ refl ⟩
    toℕ (f2f $ f'' x z) ≡⟨ F2fVeritas.mleca (f'' x z) m' ▹ sym ⟩
    toℕ (fromℕ $ f' x z) ≡⟨ DFP.toℕ-fromℕ _ ⟩
    f' x z ∎
    where
    f' = f on toℕ
    f'' = fromℕ ∘₂ f'
    m' = m ▹_ $ subst (ℕ._< _) $ DFP.toℕ-fromℕ _ ▹ sym

  dubjavmau : {n : ℕ}
            → (f : Op₂ ℕ)
            → (x z : Fin $ suc n)
            → ¬_ $ (f on toℕ) x z ℕ.< suc n
            → toℕ (f𝔽 f x z) ≡ n
  dubjavmau {n} f x z j = begin
    toℕ (f𝔽 f x z) ≡⟨ refl ⟩
    toℕ (f2f $ fromℕ $ f' x z) ≡⟨ refl ⟩
    toℕ (mFd $ decToMaybe $ f'' x z ℕ.<? _ ) ≡⟨ refl ⟩
    _ ≡⟨ DN ▹ proj₂ ▹  cong (toℕ ∘ mFd ∘ decToMaybe) ⟩
    toℕ (fromℕ< $ DNP.n<1+n _ ) ≡⟨ DFP.toℕ-fromℕ< _ ⟩
    n ∎
    where
    mFd = maybe fromℕ< $ fromℕ< $ DNP.n<1+n _
    f' = f on toℕ
    f'' = toℕ ∘₂ fromℕ ∘₂ f'
    DN = Relation.Nullary.Decidable.dec-no (f'' x z ℕ.<? _) j'
      where
      j' = j ▹ subst (¬_ ∘ (ℕ._< suc n)) (DFP.toℕ-fromℕ _ ▹ sym)
\end{code}

\section{la'oi .\F{coerce}.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi la'oi .\F{coerce}.\ bau la .lojban.

\begin{code}
coerce : ∀ {a} → {A B : Set a} → A ≡ B → A → B
coerce refl = id
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{coerce}.\ mapti}

\begin{code}
module CoerceVeritas where
  reflek : ∀ {a} → {A : Set a}
         → (x : A)
         → x ≡ coerce refl x
  reflek _ = refl

  flipko : ∀ {a} → {A B : Set a}
         → (x : A)
         → (d : A ≡ B)
         → x ≡_ $ x ▹ coerce d ▹ coerce (sym d)
  flipko _ refl = refl
\end{code}

\section{la'oi .\F{fromList?}.}
ni'o ga jo la'oi .\AgdaInductiveConstructor{nothing}.\ jonai la'o zoi.\ \AgdaInductiveConstructor{just} \B x\ .zoi.\ cu du la'o zoi.\ \F{mapₘ} \F{toList} \OpF \$ \F{fromList?} \B x\ .zoi.

\begin{code}
fromList? : ∀ {a} → {A : Set a} → {n : ℕ}
          → List A
          → Maybe $ Vec A n
fromList? v = mapₘ kofrol $ decToMaybe $ _ ≟ _
  where
  kofrol = λ c → fromList v ▹ coerce (c ▹ cong (Vec _))
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{fromList?}.\ mapti}

\begin{code}
module FromList?Veritas where
  mapdus : ∀ {a} → {A : Set a} → {n : ℕ}
         → (x : List A)
         → (∃ $ λ i → _≡_
             (mapₘ toList $ fromList? {n = n} x)
             (flip lookup i $ nothing ∷ just x ∷ []))
  mapdus = {!!}
\end{code}

\section{la'oi .\F{resize}.}
ni'o ga jonai la'o zoi.\ \F{\AgdaUnderscore{}++\AgdaUnderscore}\ \OpF \$\ \F{replicate} \B t\ .zoi.\ du ko'a goi la'o zoi.\ \F{resize}\ \Sym\{\AgdaUnderscore\Sym\} \Sym\{\B m\Sym\} \Sym\{\B n\Sym\}\ \B t\ .zoi.\ gi ga je ctaipe la'o zoi.\ \B n\ \OpF{ℕ.≤}\ \B m\ .zoi.\ gi ko'a du la'o zoi.\ \F{drop}\ \OpF \$\ \B m\ \OpF ∸\ \B n\ .zoi.

\begin{code}
module Resize where
  coc : ∀ {a} → {m n : ℕ} → {A : Set a}
      → n ℕ.≤ m
      → Vec A m ≡ Vec A (m ∸ n + n)
  coc z = DNP.m∸n+n≡m z ▹ cong (Vec _) ▹ sym

  bitc : ∀ {a} → {m n : ℕ} → {A : Set a}
       → ¬_ $ n ℕ.≤ m
       → Vec A (n ∸ m + m) ≡ Vec A n
  bitc z = DNP.m∸n+n≡m (DNP.≰⇒≥ z) ▹ cong (Vec _)

  xt : ∀ {a} → {m n : ℕ} → {A : Set a}
     → A → Vec A m → Dec (n ℕ.≤ m) → Vec A n
  xt {_} {m} {n} x xs (yes z) = drop (m ∸ n) $ coerce (coc z) xs
  xt {_} {m} {n} x xs (no z) = padin ++ xs ▹ coerce (bitc z)
    where
    padin : Vec _ $ n ∸ m
    padin = replicate x

  resize : ∀ {a} → {m n : ℕ} → {A : Set a}
         → A → Vec A m → Vec A n
  resize x xs = xt x xs $ _ ℕ.≤? _

open Resize
  using (
    resize
  )
\end{code}

\subsection{le su'u pilno le la'oi .\F{xt}.\ co'e jenai lo zo'oi .\AgdaKeyword{with}.\ co'e}
ni'o lo nu basti ko'a goi le la'oi .\F{xt}.\ co'e cu rinka lo nu nandu fa lo nu ciksi la'oi .\F{flipko}.\ je zo'e

.i la .varik.\ cu milxe le ka ce'u se fegli ko'a\ldots kei jenai ku'i cu birti lo du'u ma kau mapti la'oi .\F{flipko}.\ je zo'e je cu mleca ko'a le ka ce'u fegli  .i ranji fa le nu la .varik.\ cu djica curmi lo nu stidi

.i la .varik.\ cu cusku dei ba le nu vo'a troci lo nu basygau le zo'oi .\AgdaKeyword{with}.\ co'e ko'a\sds  .i lo du'u tcidu dei cu .indika le du'u fliba

\subsubsection{le se zvati}
ni'o xu cadga fa lo nu ko'a goi la'au le se zvati li'u me'oi .Agda.\ pinka\sds  .i la'oi .\F{resize}.\ du lo ro se srana be ko'a

\subsection{le ctaipe be le su'u la'oi .\F{resize}.\ mapti}

\begin{code}
module ResizeVeritas where
  open Resize

  open CoerceVeritas
    using (
      flipko
    )

  open ≡-Reasoning

  dropis : ∀ {a} → {m n : ℕ} → {A : Set a}
         → (x : A)
         → (xs : Vec A m)
         → (g : n ℕ.≤ m)
         → let v≡v = DNP.m∸n+n≡m g ▹ cong (Vec A) in
           let xs' = xs ▹ coerce (sym v≡v) in
           xs ≡_ $ take (m ∸ n) xs' ++ resize x xs ▹ coerce v≡v
  dropis {_} {m} {n} {A} x xs g = sym $ begin
    coerce k konk₁ ≡⟨ resize≡xt ▹ cong (coerce k ∘ _++_ _) ⟩
    coerce k konk ≡⟨ DVP.take-drop-id (m ∸ n) xs' ▹ cong (coerce k) ⟩
    coerce k xs' ≡⟨ symref k ▹ cong (flip coerce xs') ⟩
    coerce (sym $ sym k) xs' ≡⟨ flipko xs (sym k) ▹ sym ⟩
    xs ∎
    where
    k = DNP.m∸n+n≡m g ▹ cong (Vec A)
    xs' = xs ▹ coerce (sym k)
    konk : Vec A $ m ∸ n + n
    konk = take (m ∸ n) xs' ++ xt x xs (yes g)
    konk₁ : Vec A $ m ∸ n + n
    konk₁ = take (m ∸ n) xs' ++ resize x xs
    symref : ∀ {a} → {A : Set a}
           → {x z : A}
           → (t : x ≡ z)
           → t ≡ sym (sym t)
    symref refl = refl
    resize≡xt : resize x xs ≡ xt x xs (yes g)
    resize≡xt = begin
      resize x xs ≡⟨ refl ⟩
      xt x xs (_ ℕ.≤? _) ≡⟨ DY ▹ proj₂ ▹ cong (xt x xs) ⟩
      xt x xs (yes $ proj₁ DY) ≡⟨ refl ⟩
      _ ≡⟨ ≤≡≤ (proj₁ DY) g ▹ cong (xt x xs ∘ yes) ⟩
      xt x xs (yes g) ∎
      where
      DY = Relation.Nullary.Decidable.dec-yes (_ ℕ.≤? _) g

  takis : ∀ {a} → {m n : ℕ} → {A : Set a}
        → (x : A)
        → (xs : Vec A m)
        → (g : ¬ (n ℕ.≤ m))
        → let DN = Relation.Nullary.Decidable.dec-no (_ ℕ.≤? _) g in
          let k = DNP.m∸n+n≡m $ DNP.≰⇒≥ $ proj₁ DN in
          let sink = k ▹ cong (Vec A) ▹ sym in
          xs ≡_ $ drop (n ∸ m) $ resize x xs ▹ coerce sink
  takis {_} {m} {n} {A} x xs g = sym $ begin
    drop (n ∸ m) konk₁ ≡⟨ resize≡xt ▹ cong (drop _ ∘ coerce (sym k)) ⟩
    drop (n ∸ m) konk ≡⟨ konkydus ▹ cong (drop _) ⟩
    drop (n ∸ m) (pad ++ xs) ≡⟨ dropdus pad xs ▹ sym ⟩
    xs ∎
    where
    pad = replicate x
    DN = Relation.Nullary.Decidable.dec-no (n ℕ.≤? m) g
    k = DNP.m∸n+n≡m (DNP.≰⇒≥ $ proj₁ DN) ▹ cong (Vec A)
    konk : Vec A $ n ∸ m + m
    konk = xt x xs (no $ proj₁ DN) ▹ coerce (sym k)
    konk₁ : Vec A $ n ∸ m + m
    konk₁ = resize x xs ▹ coerce (sym k)
    konkydus : konk ≡ pad ++ xs
    konkydus = flipko (pad ++ xs) k ▹ sym
    resize≡xt : resize x xs ≡ xt x xs (no $ proj₁ DN)
    resize≡xt = DN ▹ proj₂ ▹ cong (xt x xs)
    dropdus : ∀ {a} → {A : Set a} → {m n : ℕ}
            → (x : Vec A m)
            → (z : Vec A n)
            → z ≡ drop (length x) (x ++ z)
    dropdus [] _ = refl
    dropdus (x ∷ xs) z = dropdus xs z ▹ subst (_ ≡_) (d xs z x)
      where
      d = λ x z e → sym $ DVP.unfold-drop (length x) e $ x ++ z
\end{code}

\section{la .\F{dist}.}
ni'o la'o zoi.\ \F{dist} \B x \B z \B d\ .zoi.\ nilzilcmi lo'i ro ctaipe be la'o zoi.\ \D{Fin} \OpF \$ \F{length} \B x\ .zoi.\ be'o poi lo meirmoi be ke'a bei fo la'oi .\B x.\ cu drata lo meirmoi be ke'a bei fo la'oi .\B x.

\begin{code}
module Dist where
  drata : ∀ {a} → {A : Set a}
        → ⦃ _ : Eq A ⦄
        → (x : A × A)
        → Dec $ false ≡_ $ isYes $ uncurry _≟_ x
  drata = _≟_ false ∘ isYes ∘ uncurry _≟_

  zipₓ : ∀ {a} → {A : Set a}
       → ⦃ Q : LL A ⦄ → ⦃ Eq $ LL.e Q ⦄
       → (x z : A)
       → LL.l Q x ≡ LL.l Q z
       → List $ LL.e Q × LL.e Q
  zipₓ x z d = toList $ zipᵥ x' z'
    where
    x' = vec x ▹_ $ coerce $ d ▹ cong (Vec _)
    z' = vec z

  dist : ∀ {a} → {A : Set a}
       → ⦃ Q : LL A ⦄ → ⦃ Eq $ LL.e Q ⦄
       → (x z : A)
       → LL.l Q x ≡ LL.l Q z
       → ℕ
  dist x z d = length $ 𝕃.filter drata $ zipₓ x z d

open Dist
  using (
    dist
  )
\end{code}

\subsection{le ctaipe be le su'u la .\F{dist}.\ cu mapti}

\begin{code}
module DistVeritas where
  open Dist
  open ≡-Reasoning

  module Zipₓ where
    len₂ : ∀ {a} → {A : Set a}
         → ⦃ Q : LL A ⦄ → ⦃ _ : Eq $ LL.e Q ⦄
         → (x z : A)
         → (d : LL.l Q x ≡ LL.l Q z)
         → length (zipₓ x z d) ≡ LL.l Q z
    len₂ ⦃ Q ⦄ x z d = begin
      length (zipₓ x z d) ≡⟨ refl ⟩
      length (toList $ zipᵥ x' $ vec z) ≡⟨ length-toList $ zipᵥ x' $ vec z ⟩
      length (zipᵥ x' $ vec z) ≡⟨ refl ⟩
      length (vec z) ≡⟨ refl ⟩
      LL.l Q z ∎
      where
      x' = vec x ▹_ $ coerce $ d ▹ cong (Vec _)
      length-toList : ∀ {a} → {A : Set a}
                    → {n : ℕ}
                    → (x : Vec A n)
                    → (_≡_
                        (length $ toList x)
                        (length x))
      length-toList [] = refl
      length-toList (_ ∷ xs) = length-toList xs ▹ cong suc

    len₁ : ∀ {a} → {A : Set a}
         → ⦃ Q : LL A ⦄ → ⦃ _ : Eq $ LL.e Q ⦄
         → (x z : A)
         → (d : LL.l Q x ≡ LL.l Q z)
         → length (zipₓ x z d) ≡ LL.l Q x
    len₁ x z d = subst (L ≡_) (sym d) $ len₂ x z d
      where
      L = length $ zipₓ x z d

  dunliv : ∀ {a} → {A : Set a} → {n : ℕ}
         → ⦃ E : Eq A ⦄
         → (x z : Vec A n)
         → (e : A)
         → dist x z refl ≡ dist (e ∷ x) (e ∷ z) refl
  dunliv x z e = sym $ begin
    dist (e ∷ x) (e ∷ z) refl ≡⟨ refl ⟩
    length (filterₗ drata $ zipₓ (e ∷ x) (e ∷ z) refl) ≡⟨ refl ⟩
    length (filterₗ drata $ (e , e) ∷ zipₓ x z refl) ≡⟨ refl ⟩
    _ ≡⟨ drats e (zipₓ x z refl) ▹ cong length ⟩
    length (filterₗ drata $ zipₓ x z refl) ≡⟨ refl ⟩
    dist x z refl ∎
    where
    filterₗ = 𝕃.filter
    drats : ∀ {a} → {A : Set a}
          → ⦃ _ : Eq A ⦄
          → (x : A)
          → (xs : List $ A × A)
          → (_≡_
              (filterₗ drata $ (x , x) ∷ xs)
              (filterₗ drata xs))
    drats = {!!}

  dratav : ∀ {a} → {A : Set a} → {n : ℕ}
         → ⦃ E : Eq A ⦄
         → (x z : Vec A n)
         → (e₁ e₂ : A)
         → ¬_ $ e₁ ≡ e₂
         → suc (dist x z refl) ≡ dist (e₁ ∷ x) (e₂ ∷ z) refl
  dratav x z e₁ e₂ j = sym $ begin
    dist (e₁ ∷ x) (e₂ ∷ z) refl ≡⟨ refl ⟩
    length (filterₗ drata $ zipₓ (e₁ ∷ x) (e₂ ∷ z) refl) ≡⟨ refl ⟩
    length (filterₗ drata $ (e₁ , e₂) ∷ zipₓ x z refl) ≡⟨ {!!} ⟩
    length ((e₁ , e₂) ∷ filterₗ drata (zipₓ x z refl)) ≡⟨ refl ⟩
    suc (length $ filterₗ drata $ zipₓ x z refl) ≡⟨ refl ⟩
    suc (dist x z refl) ∎
    where
    filterₗ = 𝕃.filter

  dubjavme'av : ∀ {a} → {A : Set a} → {n : ℕ}
              → ⦃ E : Eq A ⦄
              → (x z : Vec A n)
              → dist x z refl ℕ.≤ n
  dubjavme'av [] [] = ℕ.z≤n
  dubjavme'av {n = n} (x ∷ xs) (z ∷ zs) with x ≟ z
  ... | yes d = dubjavme'av xs zs ▹ DNP.≤-step
  ... | no d = dubjavme'av xs zs ▹ ℕ.s≤s
\end{code}

\section{la .\F{pausyk}.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu vo'a ciksi la .\F{pausyk}.\ bau la .lojban.

\begin{code}
pausyk : (b e : ℕ) → ∃ $ (_≡ suc b ^ e) ∘ suc
pausyk _ 0 = 0 , refl
pausyk b' (suc e) = _ , sym mips
  where
  mips = begin
    b ^ suc e ≡⟨ refl ⟩
    b * (b ^ e) ≡⟨ sym $ cong (b *_) $ proj₂ $ pausyk b' e ⟩
    b * suc z₁ ≡⟨ refl ⟩
    b * (1 + z₁) ≡⟨ cong (b *_) $ DNP.+-comm 1 z₁ ⟩
    b * (z₁ + 1) ≡⟨ DNP.*-distribˡ-+ b z₁ 1 ⟩
    b * z₁ + b * 1 ≡⟨ cong bizum $ DNP.*-identityʳ b ⟩
    b * z₁ + b ≡⟨ refl ⟩
    b * z₁ + (1 + b') ≡⟨ cong bizum $ DNP.+-comm 1 b' ⟩
    b * z₁ + (b' + 1) ≡⟨ sym $ DNP.+-assoc (b * z₁) b' 1 ⟩
    b * z₁ + b' + 1 ≡⟨ flip DNP.+-comm 1 $ bizum b' ⟩
    suc (b * z₁ + b') ∎
    where
    z₁ = proj₁ $ pausyk b' e
    b = suc b'
    bizum = b * z₁ +_
    open ≡-Reasoning
\end{code}

\section{la \F{panci}}
ni'o ga jonai la'oi .\AgdaInductiveConstructor{nothing}.\ du ko'a goi la'o zoi.\ \F{panci} \B k\ .zoi.\ gi ga je ctaipe la'o zoi.\ \F{nu,iork} \B k\ .zoi.\ gi ko'a me'oi .\AgdaInductiveConstructor{just}.\ la .\B k.

\begin{code}
panci : ∀ {a} → {A : Set a}
      → ⦃ L : LL A ⦄ → ⦃ Eq $ LL.e L ⦄
      → A
      → Maybe A
panci v = mapₘ (const v) $ decToMaybe $ Dec (nu,iork v) ∋ _ ≟ _
\end{code}

\subsection{le ctaipe be le su'u la \F{panci}\ cu mapti}

\begin{code}
module PanciVertias where
  nu,iork→just : ∀ {a} → {A : Set a}
               → ⦃ L : LL A ⦄ → ⦃ _ : Eq $ LL.e L ⦄
               → (x : A)
               → nu,iork x
               → panci x ≡ just x
  nu,iork→just x n = dec-yes (_ ≟ _) n ▹ proj₂ ▹ cong f
    where
    f = mapₘ (λ _ → x) ∘ decToMaybe
    dec-yes = Relation.Nullary.Decidable.dec-yes

  just→nu,iork : ∀ {a} → {A : Set a}
               → ⦃ L : LL A ⦄ → ⦃ _ : Eq $ LL.e L ⦄
               → (x : A)
               → panci x ≡ just x
               → nu,iork x
  just→nu,iork = {!!}

  ¬[nu,iork]→nothing : ∀ {a} → {A : Set a}
                     → ⦃ L : LL A ⦄ → ⦃ _ : Eq $ LL.e L ⦄
                     → (x : A)
                     → ¬_ $ nu,iork x
                     → panci x ≡ nothing
  ¬[nu,iork]→nothing x j = dec-no (_ ≟ _) j ▹ proj₂ ▹ cong f
    where
    f = mapₘ (const x) ∘ decToMaybe

  nothing→¬[nu,iork] : ∀ {a} → {A : Set a}
                     → ⦃ L : LL A ⦄ → ⦃ _ : Eq $ LL.e L ⦄
                     → (x : A)
                     → panci x ≡ nothing
                     → ¬_ $ nu,iork x
  nothing→¬[nu,iork] = {!!}

  xor : ∀ {a} → {A : Set a}
      → ⦃ L : LL A ⦄ → ⦃ _ : Eq $ LL.e L ⦄
      → (x : A)
      → ∃ $ (panci x ≡_) ∘ lookup (just x ∷ nothing ∷ [])
  xor x with Dec (nu,iork x) ∋ _ ≟ _
  ... | yes n = zero , refl
  ... | no _ = suc zero , refl

  dratan : ∀ {a} → {A : Set a}
         → ⦃ L : LL A ⦄ → ⦃ _ : Eq $ LL.e L ⦄
         → (x : A)
         → (n₁ n₂ : Fin _)
         → (_≡_ on lookup (vec x)) n₁ n₂
         → ¬_ $ n₁ ≡ n₂
         → panci x ≡ nothing
  dratan = {!!}
\end{code}

\section{la .\F{indice}}
ni'o ro da poi ke'a ctaipe la'o zoi.\ \D{Fin} \AgdaUnderscore{}\ .zoi.\ zo'u lo meirmoi be da bei fo la'o zoi.\ \F{indice} \B x\ .zoi.\ .orsi li re fo da fi lo meirmoi be da bei fo la'oi .\B{x}.

\begin{code}
indice : ∀ {a} → {A : Set a} → {n : ℕ}
       → Vec A n
       → flip Vec n $ A × Fin n
indice = flip zipᵥ $ allFin _
\end{code}

\subsection{le ctaipe be le su'u la .\F{indice}\ cu mapti}

\begin{code}
module IndiceVeritas where
  ordun : ∀ {a} → {A : Set a} → {n : ℕ}
        → (x : Vec A n)
        → <_,_> (lookup x) id ≗ lookup (indice x)
  ordun x i = Function.Inverse.f DPP.×-≡,≡↔≡ $ R , P
    where
    open ≡-Reasoning
    R = sym $ begin
      proj₁ (lookup (indice x) i) ≡⟨ refl ⟩
      proj₁ (lookup (zipᵥ x $ allFin _) i) ≡⟨ refl ⟩
      _ ≡⟨ DVP.lookup-zip i x _ ▹ cong proj₁ ⟩
      proj₁ (lookup x i , lookup (allFin _) i) ≡⟨ refl ⟩
      lookup x i ∎
    P = sym $ begin
      proj₂ (lookup (indice x) i) ≡⟨ refl ⟩
      _ ≡⟨ DVP.lookup-zip i x _ ▹ cong proj₂ ⟩
      lookup (allFin _) i ≡⟨ DVP.lookup-allFin i ⟩
      i ∎

  rev : ∀ {a} → {A : Set a} → {n : ℕ}
      → ⦃ _ : Eq A ⦄
      → (x : Vec A n)
      → (e : A × Fin (length x))
      → e Truthbrary.Record.LLC.∈ indice x
      → Data.Vec.lookup x (proj₂ e) ≡ proj₁ e
  rev = {!!}
\end{code}

\section{la'o zoi.\ \F{toVec?}\ .zoi.}
ni'o la .varik.\ na birti lo du'u ma kau zabna je cu lojbo je cu velcki la'o zoi.\ \F{toVec?}\ .zoi.

\begin{code}
toVec? : ∀ {a} → {A : Set a} → {n : ℕ}
       → List A
       → Maybe $ Vec A n
toVec? l = dun? ▹ mapₘ (λ n → fromList l ▹ coerce (vk n))
  where
  vk = cong $ Vec _
\end{code}

\chap{le fancu co ke porsi be lo'i me'oi .bit.\ ke'e}

\section{la'oi .\F{nbits}.}
ni'o ko'a goi la'o zoi.\ \F{nbits} \B q\ .zoi.\ porsi lo'i su'o me'oi .bit.\ poi ke'a pagbu la'oi .\B q.\sds  .i ga je lo pamoi be ko'a cu traji le ka ce'u me'oi .significant.\ kei le ka ce'u zenba gi lo romoi be ko'a cu traji le ka ce'u me'oi .significant.\ kei le ka ce'u mleca

.i la'oi .\F{nbits}.\ simsa la'o zoi.\ \F{Data.Bin.toBits}\ .zoi.\ je ku'i cu me'oi .truncate.

\begin{code}
nbits : {n : ℕ} → ℕ → Vec (Fin 2) n
nbits = resize zero ∘ fromList ∘ reverse ∘ proj₁ ∘ toDigits 2
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{nbits}.\ mapti}

\begin{code}
module NbitsVeritas where
  zeros : {n : ℕ} → nbits {n} 0 ≡ replicate zero
  zeros {n} = begin
    nbits {n} 0 ≡⟨ {!!} ⟩
    replicate zero ∎
    where
    open ≡-Reasoning

  meirmoi : {n x : ℕ}
          → (f : Fin n)
          → lookup (nbits {n} x) f ≡ {!!}
  meirmoi = {!!}
\end{code}

\section{la'oi .\F{b2f}.}
ni'o la'o zoi.\ \F{toℕ} \OpF \$ \F{b2f} \B x\ .zoi.\ selsni la'oi .\B x.\ noi .endi le me'oi .big.

\begin{code}
module B2f where
  indice' : ∀ {a} → {A : Set a} → {n : ℕ}
          → Vec A n → Vec (A × Fin n) n
  indice' = flip zipᵥ $ reverseᵥ $ allFin _

  sumᵥ' : {m n : ℕ} → Vec (Fin $ suc m) n → Fin $ suc m
  sumᵥ' = foldrᵥ _ (f𝔽 _+_) zero

  portenfa₁ : {m' n : ℕ}
            → let m = suc m' in
              (flip Vec
                n
                (_×_
                  (Fin $ suc $ proj₁ $ pausyk m' n)
                  (Fin n)))
            → Fin $ m ^ n
  portenfa₁ {m'} {n} = coerce k ∘ sumᵥ' ∘ mapᵥ tefpi'i
    where
    m = suc m'
    k = cong Fin $ proj₂ $ pausyk m' n
    tefpi'i = uncurry (f𝔽 $ λ a b → a * m ^ b) ∘ map₂ f2f

  portenfa : {m n : ℕ}
           → flip Vec n $ Fin $ suc $ proj₁ $ pausyk m n
           → Fin $ suc m ^ n
  portenfa = portenfa₁ ∘ indice'

  b2f : {m : ℕ} → Vec (Fin $ suc m) ⊆ Fin ∘ suc m ^_
  b2f = portenfa ∘ mapᵥ f2f

open B2f
  using (
    b2f
  )
\end{code}

\subsection{le se zvati}
ni'o xu cadga fa lo nu muvgau le velcki be ko'a goi la'oi .\F{b2f}.\ lo drata be la'au \chapsname\ li'u\sds  .i ko'a mapti lo na ctaipe be ko'e goi la'o zoi.\ \D{Fin} \AgdaNumber 2\ .zoi.\ je ku'i cu co'e ja selbi'o pe'a zo'e poi ctaipe ko'e fa lo ro mapti be ke'a\sds  .i la .varik.\ na birti lo du'u ma kau ckupau je cu zmadu la'au \chapsname\ li'u le ka ko'a mapti ce'u

\subsection{le ctaipe be le su'u la'oi .\F{b2f}.\ mapti}

\begin{code}
module B2fVeritas where
  open ≡-Reasoning

  module Sumᵥ' where
    sumᵥ'₂ : {m n : ℕ} → Vec (Fin $ suc m) n → Fin $ suc m
    sumᵥ'₂ {m} x = maybe fromℕ< (fromℕ m) mleca?
      where
      mleca? = decToMaybe $ sumᵥ (mapᵥ toℕ x) ℕ.<? suc m

    pav : {m : ℕ}
        → (f : Fin $ suc m)
        → B2f.sumᵥ' (f ∷ []) ≡ f2f f
    pav f = begin
      B2f.sumᵥ' (f ∷ []) ≡⟨ refl ⟩
      foldrᵥ _ (f𝔽 _+_) zero (f ∷ []) ≡⟨ refl ⟩
      f𝔽 _+_ f zero ≡⟨ refl ⟩
      f2f (fromℕ $ toℕ f + 0) ≡⟨ refl ⟩
      _ ≡⟨ DNP.+-identityʳ (toℕ f) ▹ cong (f2f ∘ fromℕ) ⟩
      f2f (fromℕ $ toℕ f) ≡⟨ F2fVeritas.fromℕ-toℕ f ⟩
      f2f f ∎

    pav₂ : {m : ℕ} → _≗_ (sumᵥ'₂ {m} ∘ (_∷ [])) f2f
    pav₂ f = begin
      sumᵥ'₂ (f ∷ []) ≡⟨ refl ⟩
      maybe fromℕ< (fromℕ _) mleca? ≡⟨ {!!} ⟩
      maybe fromℕ< (fromℕ _) mleca?₂ ≡⟨ refl ⟩
      _ ≡⟨ DFP.fromℕ-def _ ▹ cong (λ n → maybe fromℕ< n mleca?₂) ⟩
      maybe fromℕ< (fromℕ< _) mleca?₂ ≡⟨ refl ⟩
      F2f.mFd (toℕ f) ≡⟨ refl ⟩
      f2f f ∎
      where
      mleca? = decToMaybe $ sumᵥ (mapᵥ toℕ $ f ∷ []) ℕ.<? suc _
      mleca?₂ = decToMaybe $ toℕ f ℕ.<? suc _

    kunti : {n : ℕ}
          → (v : Vec (Fin $ suc n) 0)
          → B2f.sumᵥ' v ≡ zero
    kunti [] = refl

    inc : {m n : ℕ}
        → (e : Fin $ suc m)
        → let _+'_ = f𝔽 _+_ in
          B2f.sumᵥ' ∘ (e ∷_) ≗ (e +'_ ∘ B2f.sumᵥ' {n = n})
    inc _ _ = refl

    inc₂ : {m n : ℕ}
         → (e : Fin $ suc m)
         → (v : Vec (Fin $ suc m) n)
         → let _+'_ = f𝔽 _+_ in
           sumᵥ'₂ (e ∷ v) ≡ e +' sumᵥ'₂ v
    inc₂ e v = begin
      sumᵥ'₂ (e ∷ v) ≡⟨ {!!} ⟩
      e +' sumᵥ'₂ v ∎
      where
      _+'_ = f𝔽 _+_

    sumᵥ'≡sumᵥ'₂ : {m n : ℕ}
                 → (x : Vec (Fin $ suc m) n)
                 → B2f.sumᵥ' x ≡ sumᵥ'₂ x
    sumᵥ'≡sumᵥ'₂ [] = refl
    sumᵥ'≡sumᵥ'₂ (x ∷ []) = begin
      B2f.sumᵥ' (x ∷ []) ≡⟨ pav x ⟩
      f2f x ≡⟨ pav₂ x ▹ sym ⟩
      sumᵥ'₂ (x ∷ []) ∎
    sumᵥ'≡sumᵥ'₂ (x ∷ xs) = begin
      B2f.sumᵥ' (x ∷ xs) ≡⟨ refl ⟩
      x +' (B2f.sumᵥ' xs) ≡⟨ sumᵥ'≡sumᵥ'₂ xs ▹ cong (x +'_) ⟩
      x +' (sumᵥ'₂ xs) ≡⟨ inc₂ x xs ▹ sym ⟩
      sumᵥ'₂ (x ∷ xs) ∎
      where
      _+'_ = f𝔽 _+_

    mleca : {m n : ℕ}
          → (v : Vec (Fin $ suc m) n)
          → (ml : sumᵥ (mapᵥ toℕ v) ℕ.< suc m)
          → B2f.sumᵥ' v ≡ fromℕ< ml
    mleca {m} {n} v ml = begin
      B2f.sumᵥ' v ≡⟨ sumᵥ'≡sumᵥ'₂ v ⟩
      sumᵥ'₂ v ≡⟨ refl ⟩
      maybe′ fromℕ< (fromℕ m) mleca? ≡⟨ refl ⟩
      _ ≡⟨ mleca?≡justml ▹_ $ cong $ maybe′ fromℕ< $ fromℕ m ⟩
      maybe′ fromℕ< (fromℕ m) (just ml) ≡⟨ refl ⟩
      fromℕ< ml ∎
      where
      mleca? = decToMaybe $ sumᵥ (mapᵥ toℕ v) ℕ.<? suc m
      mleca?≡justml = begin
        mleca? ≡⟨ refl ⟩
        decToMaybe (sumᵥ (mapᵥ toℕ v) ℕ.<? suc m) ≡⟨ refl ⟩
        _ ≡⟨ DY ▹ proj₂ ▹ cong decToMaybe ⟩
        decToMaybe (yes $ DY ▹ proj₁) ≡⟨ refl ⟩
        just (DY ▹ proj₁) ≡⟨ ≤≡≤ _ _ ▹ cong just ⟩
        just ml ∎
        where
        open Relation.Nullary.Decidable using (dec-yes)
        DY = dec-yes (_ ℕ.<? _) ml 

    dubjavmau : {m n : ℕ}
              → (v : Vec (Fin $ suc m) n)
              → ¬_ $ sumᵥ (mapᵥ toℕ v) ℕ.< suc m
              → B2f.sumᵥ' v ≡ fromℕ m
    dubjavmau {m} {n} v J = begin
      B2f.sumᵥ' v ≡⟨ sumᵥ'≡sumᵥ'₂ v ⟩
      sumᵥ'₂ v ≡⟨ refl ⟩
      maybe′ F (fromℕ m) mleca? ≡⟨ refl ⟩
      _ ≡⟨ K ▹_ $ cong $ maybe′ F $ fromℕ m ⟩
      maybe′ F (fromℕ m) nothing ≡⟨ refl ⟩
      fromℕ m ∎
      where
      F = fromℕ< {_}
      mleca? = decToMaybe $ sumᵥ (mapᵥ toℕ v) ℕ.<? suc m
      K : mleca? ≡ nothing
      K = dec-no _ J ▹ proj₂ ▹ cong decToMaybe
        where
        open Relation.Nullary.Decidable using (dec-no)

    du : {m n : ℕ}
       → (v : Vec (Fin $ suc m) n)
       → toℕ (B2f.sumᵥ' v) ≡ m ℕ.⊓ sumᵥ (mapᵥ toℕ v)
    du {m} {n} v with sumᵥ (mapᵥ toℕ v) ℕ.<? suc m
    ... | yes M = begin
      toℕ (B2f.sumᵥ' v) ≡⟨ mleca v M ▹ cong toℕ ⟩
      toℕ (fromℕ< M) ≡⟨ DFP.toℕ-fromℕ< M ⟩
      sumᵥ (mapᵥ toℕ v) ≡⟨ DNP.m≥n⇒m⊓n≡n (<⇒≤ M) ▹ sym ⟩
      m ℕ.⊓ sumᵥ (mapᵥ toℕ v) ∎
      where
      <⇒≤ : {m n : ℕ} → m ℕ.< suc n → m ℕ.≤ n
      <⇒≤ (ℕ.s≤s x) = x
    ... | no d = begin
      toℕ (B2f.sumᵥ' v) ≡⟨ dubjavmau v d ▹ cong toℕ ⟩
      toℕ (fromℕ m) ≡⟨ DFP.toℕ-fromℕ _ ⟩
      m ≡⟨ DNP.m≤n⇒m⊓n≡m (s≤⇒≤ $ DNP.≮⇒≥ d) ▹ sym ⟩
      m ℕ.⊓ sumᵥ (mapᵥ toℕ v) ∎
      where
      s≤⇒≤ : {m n : ℕ} → suc m ℕ.≤ n → m ℕ.≤ n
      s≤⇒≤ {0} (ℕ.s≤s x) = ℕ.z≤n
      s≤⇒≤ {suc _} (ℕ.s≤s x) = ℕ.s≤s $ s≤⇒≤ x

  module Indice' where
    indice'v : ∀ {a} → {A : Set a} → {n : ℕ}
             → (v : Vec A n)
             → (i : Fin n)
             → (_≡_
                 (lookup (B2f.indice' v) i)
                 (lookup v i , 𝔽.opposite i))
    indice'v {n = n} v i = begin
      lookup (B2f.indice' v) i ≡⟨ refl ⟩
      L (B2f.indice' v) ≡⟨ refl ⟩
      L (flip zipᵥ (reverseᵥ $ allFin _) v) ≡⟨ refl ⟩
      L (zipᵥ v $ reverseᵥ $ allFin _) ≡⟨ refl ⟩
      _ ≡⟨ DVP.lookup-zip i v _ ⟩
      L v , L (reverseᵥ $ allFin _) ≡⟨ refl ⟩
      _ ≡⟨ oppositevec _ ▹ cong (λ x → L v , L x) ⟩
      L v , L (mapᵥ o $ allFin _) ≡⟨ refl ⟩
      _ ≡⟨ DVP.lookup-map i o (allFin _) ▹ cong (L v ,_) ⟩
      L v , o (L $ allFin _) ≡⟨ refl ⟩
      _ ≡⟨ DVP.lookup-allFin i ▹ cong (λ x → L v , o x) ⟩
      lookup v i , o i ∎
      where
      o = 𝔽.opposite
      L : ∀ {a} → {A : Set a} → Vec A n → A
      L = flip lookup i
      oppositevec : (n : ℕ)
                  → reverseᵥ (allFin n) ≡ mapᵥ o (allFin n)
      oppositevec 0 = refl
      oppositevec (suc n) = begin
        reverseᵥ (allFin $ suc n) ≡⟨ reverse-allFin-∷ ⟩
        o zero ∷ mapᵥ 𝔽.inject₁ (reverseᵥ $ allFin n) ≡⟨ refl ⟩
        _ ≡⟨ {!!} ▹ cong (λ n → o zero ∷ mapᵥ 𝔽.inject₁ n) ⟩
        o zero ∷ mapᵥ 𝔽.inject₁ (mapᵥ o $ allFin n) ≡⟨ o-allFin-∷ ▹ sym ⟩
        mapᵥ o (allFin $ suc n) ∎
        where
        reverse-allFin-∷ : {n : ℕ}
                         → (_≡_
                             (reverseᵥ $ allFin $ suc n)
                             (_∷_
                               (o zero)
                               (mapᵥ
                                 𝔽.inject₁
                                 (reverseᵥ $ allFin n))))
        reverse-allFin-∷ {0} = {!!}
        reverse-allFin-∷ {suc n} = {!!}
        o-allFin-∷ : {n : ℕ}
                   → (_≡_
                       (mapᵥ o $ allFin $ suc n)
                       (_∷_
                         (o zero)
                         (mapᵥ
                           𝔽.inject₁
                           (mapᵥ o $ allFin n))))
        o-allFin-∷ {0} = begin
          mapᵥ o (allFin $ suc 0) ≡⟨ {!!} ⟩
          o zero ∷ mapᵥ 𝔽.inject₁ (mapᵥ o $ allFin 0) ∎
        o-allFin-∷ {suc n} = {!!}

  module Portenfa where
    non : {m : ℕ} → B2f.portenfa {m} [] ≡ zero
    non = refl

    jmina : {m n : ℕ}
          → (x : _)
          → (xs : Vec _ n)
          → (_≡_
              (B2f.portenfa {m} $ x ∷ xs)
              (flip mink
                (pausyk m (suc n) ▹ proj₂)
                (f𝔽 _+_
                  (fromℕ< {toℕ x * m ^ suc n} {!!})
                  {!!})))
    jmina = {!!}

    -- | ni'o la .varik. cu djica lo nu basti pe'a ko'a
    -- goi le me'oi .f2f. co'e fa lo zmadu be ko'a bei le
    -- ka tu'a ce'u .indika... kei kei jenai ku'i cu birti
    -- lo du'u ma kau zmadu... kei je ku'i cu djica curmi
    -- lo nu stidi
    jminan : {m n : ℕ}
           → (x : _)
           → (xs : Vec _ n)
           → (_≡_
               (toℕ $ B2f.portenfa {m} {suc n} $ x ∷ xs)
               (_+_
                 (toℕ x * suc m ^ suc n)
                 (toℕ $ B2f.portenfa {m} {n} $ xs ▹ mapᵥ f2f)))
    jminan = {!!}

  kunti : (m : ℕ) → b2f {m} [] ≡ zero
  kunti _ = refl

  non' : (m n : ℕ)
       → (flip _≡_
           (mink zero $ proj₂ $ pausyk m n)
           (b2f $ replicate {n = n} $ zero {m}))
  non' _ 0 = refl
  non' m (suc n) = {!!}

  non : (m n : ℕ)
      → (_≡ 0) $ toℕ $ b2f $ replicate {n = n} $ zero {m}
  non m n = begin
    toℕ (b2f $ replicate {n = n} $ zero) ≡⟨ non' m n ▹ cong toℕ ⟩
    toℕ (mink zero $ pausyk m n ▹ proj₂ ) ≡⟨ tomindus _ _ ▹ sym ⟩
    0 ∎

  mulj : (m n : ℕ)
       → (x : Fin $ suc m)
       → (xs : Vec (Fin $ suc m) n)
       → toℕ (b2f $ x ∷ xs) ≡ toℕ (b2f xs) + toℕ x * suc m ^ n
  mulj m 0 x [] = begin
    toℕ (b2f $ x ∷ []) ≡⟨ refl ⟩
    toℕ (B2f.portenfa {m} $ mapᵥ f2f $ x ∷ []) ≡⟨ refl ⟩
    toℕ (B2f.portenfa {m} $ f2f x ∷ []) ≡⟨ refl ⟩
    toℕ (B2f.portenfa₁ {m} $ B2f.indice' $ f2f x ∷ []) ≡⟨ refl ⟩
    toℕ (B2f.portenfa₁ {m} $ (f2f x , zero) ∷ []) ≡⟨ {!!} ⟩
    toℕ (b2f {m} []) + toℕ x * suc m ^ 0 ∎
  mulj m (suc n) x (z ∷ zs) = {!!}
\end{code}

\section{le su'u la'oi .\F{nbits}.\ srana la'oi .\F{b2f}.\ldots je la'oi .\F{toℕ}.}
ni'o la .varik.\ cu stidi lo nu lo na jimpe cu tcidu lo lojbo je velcki be le fancu poi ke'a srana

\begin{code}
module B2f-toℕ where
  toℕ∘b2f∘nbits : {n : ℕ}
                → (x : ℕ)
                → 2 ^ n ℕ.> x
                → x ≡_ $ toℕ $ b2f {x = n} $ nbits x
  toℕ∘b2f∘nbits = {!!}
\end{code}

\section{la .\F{cunsof}.}
ni'o la .\F{cunsof}.\ cu me'oi .\F{pure}.\ lo me'oi .pseudorandom.

ni'o zo .cunsof.\ cmavlaka'i lu cunso .fin.\ li'u

\begin{code}
cunsof : {n : ℕ} → IO $ Fin $ 2 ^ n
cunsof {n} = b2f ∘ mapᵥ sb2f <$> cunvek n
  where
  sb2f = λ n → if n then suc zero else zero
  cunvek : (n : ℕ) → IO $ Vec Bool n
  cunvek n = sequenceᵥ cunste
    where
    sequenceᵥ : ∀ {a} → {A : Set a} → {n : ℕ}
              → Vec (IO A) n
              → IO $ Vec A n
    sequenceᵥ [] = pure []
    sequenceᵥ (x ∷ xs) = x IO.>>= λ x' → (x' ∷_) IO.<$> sequenceᵥ xs
    cunste : {n : ℕ} → Vec (IO Bool) n
    cunste = replicate $ IO.lift cunsob
      where
      -- | ni'o cadga fa lo nu la'o zoi. cunsob n .zoi.
      -- me'oi .pure. lo me'oi .pseudorandom.
      postulate cunsob : ABIO.IO Bool
      {-#
        FOREIGN GHC
        import qualified Data.ByteString.Lazy as BSL
      #-}
      {-#
        COMPILE GHC
        cunsob = head . map (== 1) . filter (< 2) <$> cunsol
          -- ni'o le me'oi .filter. co'e cu masno je
          -- ku'i cu filri'a lo nu na mutce le ka ce'u
          -- cafne kei fa lo nu li no zmadu li pa le ka
          -- me'oi .pure. ce'u
          where
          cunsol = BSL.unpack <$> BSL.readFile "/dev/random"
      #-}
\end{code}

\subsection{tu'a le se ctaipe be la .\F{cunsof}.}
ni'o la .varik.\ cu djica lo nu la .\F{cunsof}.\ cu ctaipe ko'a goi la'o zoi.\ \Sym\{\B n \Sym : \D ℕ\Sym\} \Sym → \D{IO} \OpF \$ \D{Fin} \OpF \$ \AgdaInductiveConstructor{suc} \B n\ .zoi.\ldots kei jenai ku'i cu birti lo du'u ma kau zabna je cu me'oi .Agda.\ velcki lo versiio be la .\F{cunsof}.\ poi ke'a ctaipe ko'a

.i la .varik.\ na djuno lo du'u ma kau filri'a lo nu lo me'oi .Haskell.\ co'e cu benji lo ctaipe be lo mapti be la'o zoi.\ \D{Fin} \B x\ .zoi.\ la'oi .Agda.  .i tu'a la'oi .\xactaipes{Bool}.\ sampu\ldots je ku'i cu mapti la'o zoi.\ \D{Fin} \AgdaNumber 2 .zoi.\ jenai zo'e

.i ji'a ga naja la .\F{cunsof}.\ cu co'e ja binxo lo ctaipe be ko'a gi cadga fa lo nu muvgau lo velcki be la .\F{cunsof}.

.i ku'i ga je ko'e goi zoi zoi.\ \F{cunsof} \Sym = \F{pure} \AgdaInductiveConstructor{zero} .zoi.\ sampu je cu mapti ko'a gi frili fa lo nu jimpe fi ko'e

\section{la'oi .\F{\AgdaUnderscore{}∧𝔹ℕ𝔽\AgdaUnderscore}.}
ni'o la'o zoi.\ \B a \OpF{∧𝔹ℕ𝔽} \B b\ .zoi.\ mu'oi glibau.\ bitwise and .glibau.\ la'oi .\B a.\ la'oi .\B b.

\begin{code}
module ∧𝔹ℕ𝔽 where
  _∧𝔹ℕ𝔽₁_ : {n : ℕ} → ℕ → Fin $ suc n → Vec (Fin _) $ suc n
  _∧𝔹ℕ𝔽₁_ a = zipWithᵥ (f𝔽 _*_) (nbits a) ∘ nbits ∘ toℕ

  _∧𝔹ℕ𝔽₁_mleca : {m : ℕ}
               → (n : ℕ)
               → (f : Fin $ suc m)
               → toℕ (b2f $ n ∧𝔹ℕ𝔽₁ f) ℕ.< suc m
  _∧𝔹ℕ𝔽₁_mleca = {!!}

  _∧𝔹ℕ𝔽_ : {n : ℕ} → ℕ → Op₁ $ Fin $ suc n
  _∧𝔹ℕ𝔽_ = fromℕ< ∘₂ _∧𝔹ℕ𝔽₁_mleca

open ∧𝔹ℕ𝔽
  using (
    _∧𝔹ℕ𝔽_
  )
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{\AgdaUnderscore{}∧𝔹ℕ𝔽\AgdaUnderscore}.\ mapti}

\begin{code}
module ∧𝔹ℕ𝔽Veritas where
  open ∧𝔹ℕ𝔽

  module _∧𝔹ℕ𝔽₁_ where

  nada : {m : ℕ} → (n : ℕ) → _∧𝔹ℕ𝔽_ {m} n zero ≡ zero
  nada {m} n = begin
    n ∧𝔹ℕ𝔽 zero ≡⟨ refl ⟩
    fromℕ< (_∧𝔹ℕ𝔽₁_mleca n zero) ≡⟨ F2fVeritas.fromℕ<-f2f _ _ ⟩
    f2f (b2f $ zW $ nbits 0) ≡⟨ refl ⟩
    toFin (zW $ nbits 0) ≡⟨ NbitsVeritas.zeros ▹ cong (toFin ∘ zW) ⟩
    toFin (zW Z) ≡⟨ zipdun ▹ cong toFin ⟩
    toFin Z ≡⟨ refl ⟩
    f2f (b2f Z) ≡⟨ f2f-zero (b2f Z) $ B2fVeritas.non 1 $ length Z ⟩
    zero ∎
    where
    toFin : Vec (Fin 2) $ suc m → Fin $ suc m
    toFin = f2f ∘ b2f
    zW = zipWithᵥ (f𝔽 _*_) $ nbits n
    Z = replicate zero
    open ≡-Reasoning
    f2f-zero = F2fVeritas.zeron
    zipdun : zipWithᵥ (f𝔽 _*_) (nbits n) Z ≡ Z
    zipdun = begin
      zipWithᵥ (f𝔽 _*_) (nbits n) Z ≡⟨ {!!} ⟩
      zipWithᵥ (f𝔽 _*_) Z (nbits n) ≡⟨ ziprep (f𝔽 _*_) zero $ nbits n ⟩
      mapᵥ (f𝔽 _*_ zero) (nbits n) ≡⟨ {!!} ⟩
      Z ∎
      where
      ziprep : ∀ {a b c}
             → {A : Set a} → {B : Set b} → {C : Set c}
             → {n : ℕ}
             → (f : A → B → C)
             → (x : A)
             → (z : Vec B n)
             → zipWithᵥ f (replicate x) z ≡ mapᵥ (f x) z
      ziprep f x [] = refl
      ziprep f x (z ∷ zs) = ziprep f x zs ▹ cong (f x z ∷_)

  idx : {m : ℕ}
      → (f : Fin $ suc m)
      → toℕ f ∧𝔹ℕ𝔽 f ≡ f
  idx {m} f = begin
    toℕ f ∧𝔹ℕ𝔽 f ≡⟨ {!!} ⟩
    f ∎
    where
    open ≡-Reasoning

  dunli : {m : ℕ}
        → (n : ℕ)
        → (_≡_
            (n ∧𝔹ℕ𝔽 opposite zero)
            (fromℕ< {n ℕ.⊓ 2 ^ m} $ DNP.m⊓n≤n _ _))
  dunli {m} n = begin
    n ∧𝔹ℕ𝔽 opposite zero ≡⟨ F2fVeritas.fromℕ<-f2f _ _ ⟩
    toFin (p $ nbits $ toℕ $ opposite $ zero {2 ^ m}) ≡⟨ {!!} ⟩
    toFin (p pav) ≡⟨ {!!} ⟩
    toFin (nbits n) ≡⟨ {!!} ⟩
    fromℕ< (DNP.m⊓n≤n _ _) ∎
    where
    pav = replicate $ suc zero
    p = zipWithᵥ (f𝔽 _*_) (nbits n)
    toFin : {m : ℕ} → Vec (Fin 2) $ suc m → Fin $ suc m
    toFin = f2f ∘ b2f
    open ≡-Reasoning
\end{code}

\section{la'oi .\F{hw𝕄}.}
ni'o la'o zoi.\ \F{hw𝕄} \B t\ .zoi.\ grisumji lo'i ro co'e poi su'o da poi ke'a xi re co'e ja rajypau la'oi .\B{t}.\ zo'u ke'a mu'oi glibau.\ HAMMING weight .glibau.\ da

\begin{code}
hw𝕄 : {a m n : ℕ} → 𝕄 (Fin a) m n → ℕ
hw𝕄 = sumᵥ ∘ mapᵥ hWV𝔽
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{hw𝕄}.\ mapti}

\begin{code}
module Hw𝕄Veritas where
  kunti₁ : {a m : ℕ} → (x : 𝕄 (Fin a) m 0) → hw𝕄 x ≡ 0
  kunti₁ [] = refl

  kunti₂ : {a m : ℕ} → (x : 𝕄 (Fin a) 0 m) → hw𝕄 x ≡ 0
  kunti₂ {a} {m} x = begin
    hw𝕄 x ≡⟨ 𝕄0≡replicate[] x ▹ cong hw𝕄 ⟩
    hw𝕄 {a} (replicate {n = m} []) ≡⟨ refl ⟩
    sumᵥ (mapᵥ hWV𝔽 $ replicate {n = m} []) ≡⟨ refl ⟩
    _ ≡⟨ DVP.map-replicate hWV𝔽 [] m ▹ cong sumᵥ ⟩
    sumᵥ (replicate {n = m} 0) ≡⟨ nosum m ⟩
    0 ∎
    where
    open ≡-Reasoning
    nosum : (m : ℕ) → sumᵥ (replicate {n = m} 0) ≡ 0
    nosum 0 = refl
    nosum (suc n) = nosum n
    𝕄0≡replicate[] : ∀ {a} → {A : Set a} → {m : ℕ}
                   → (x : 𝕄 A 0 m)
                   → x ≡ replicate {n = m} []
    𝕄0≡replicate[] [] = refl
    𝕄0≡replicate[] ([] ∷ xs) = R ▹ cong (_ ∷_)
      where
      R = 𝕄0≡replicate[] xs

  pav : {a m : ℕ}
      → (e : Vec (Fin a) m)
      → hw𝕄 (e ∷ []) ≡ hWV𝔽 e
  pav e = begin
    hw𝕄 (e ∷ []) ≡⟨ refl ⟩
    sumᵥ (mapᵥ hWV𝔽 $ e ∷ []) ≡⟨ refl ⟩
    sumᵥ (hWV𝔽 e ∷ []) ≡⟨ refl ⟩
    hWV𝔽 e + 0 ≡⟨ DNP.+-identityʳ _ ⟩
    hWV𝔽 e ∎
    where
    open ≡-Reasoning

  jminas : {a m n : ℕ}
         → (x : 𝕄 (Fin a) m n)
         → (e : Vec (Fin a) m)
         → hw𝕄 (e ∷ x) ≡ hWV𝔽 e + hw𝕄 x
  jminas _ _ = refl

  jminas₂ : {a m n : ℕ}
          → (x : 𝕄 (Fin a) m n)
          → (e : Vec (Fin a) m)
          → hw𝕄 (e ∷ x) ≡ hw𝕄 (e ∷ []) + hw𝕄 x
  jminas₂ x e = jminas x e ▹ subst (_≡_ _) (pav' x e)
    where
    pav' = λ x e → pav e ▹ sym ▹ cong (_+ hw𝕄 x)
\end{code}

\section{la'oi .\F{moult}.}
ni'o la'o zoi.\ \F{moult}\ \B a\ \B b\ .zoi.\ pilji la'oi .\B{a}.\ la'oi .\B{b}.

\begin{code}
moult : {m n o : ℕ} → 𝕄 (Fin 2) m n → Vec (Fin 2) o
      → Vec (Fin 2) n
moult = {!!}
\end{code}

\chap{la'oi .\AgdaRecord{MCParam}.\ je zo'e}
ni'o la'au \chapsname\ li'u vasru le velcki be ko'a goi la'oi .\AgdaRecord{MCParam}.\ be'o je le pinka be ko'a be'o je ko'a goi le fancu poi ke'a srana la'oi .\AgdaRecord{MCParam}.\ po'o ku'o je le pinka be ko'a

\section{la'oi .\AgdaRecord{MCParam}.}
ni'o la'oi .\AgdaRecord{MCParam}.\ se ctaipe lo me'oi .parameter.\ lo mu'oi glibau.\ Classic MCELIECE .glibau.\ co'e

\subsection{le me'oi .\AgdaKeyword{field}.}

\subsubsection{le vrici je me'oi .\AgdaKeyword{field}.}
\paragraph{la'oi .\AgdaField{MCParam.n}.}
ni'o la'o zoi.\ \AgdaField{MCParam.n} \B q\ .zoi.\ ni clani fa lo me'oi .code.\ pe la'oi .\B{q}.

\paragraph{la'oi .\AgdaField{MCParam.m}.}
ni'o la'o zoi.\ \AgdaField{MCParam.m} \B q\ .zoi.\ reldugri lo ni barda fa lo co'e ja selvau be lo me'oi .\AgdaKeyword{field}.

\paragraph{la'oi .\AgdaField{MCParam.t}.}
ni'o la'o zoi.\ \AgdaField{MCParam.t} \B q\ .zoi.\ ni cumki fa lo nu rinka ja gasnu ja co'e lo nu binxo lo drani

\paragraph{la'oi .\AgdaField{MCParam.f}.}
ni'o la'o zoi.\ \AgdaField{MCParam.f} \B q\ .zoi.\ me'oi .monic.\ je me'oi .irreducible.\ cpolynomi'a fi la'o zoi.\ \AgdaField{MCParam.m} \B q\ .zoi\ldots je cu co'e

\paragraph{la'oi .\AgdaField{MCParam.F}.}
ni'o la'o zoi.\ \AgdaField{MCParam.F} \B q\ .zoi.\ me'oi .monic.\ je me'oi .irreducible.\ cpolynomi'a fi la'o zoi.\ \AgdaField{MCParam.t} \B q\ .zoi\ldots je cu co'e

\paragraph{la'oi .\AgdaField{MCParam.k}.}
ni'o la'o zoi.\ \AgdaField{MCParam.k} \B q\ .zoi.\ me'oi .dimension.\ lo me'oi .code.\ pe la'oi .\B q.

\paragraph{la'oi .\AgdaField{MCParam.ν}.}
ni'o la'o zoi.\ \AgdaField{MCParam.ν} \B q\ .zoi.\ dubjavmau li no je cu dubjavme'a lo sumji be la'o zoi.\ \AgdaField{MCParam.k} \B q\ .zoi.\ bei la'o zoi.\ \AgdaField{MCParam.μ} \B q\ .zoi.

\paragraph{la'oi .\AgdaField{MCParam.ν}.}
ni'o la'o zoi.\ \AgdaField{MCParam.μ} \B q\ .zoi.\ dubjavmau li no je cu dubjavme'a la'o zoi.\ \AgdaField{MCParam.ν} \B q\ .zoi.\ je lo vujnu be la'o zoi.\ \AgdaField{MCParam.ν} \B q\ .zoi.\ bei la'o zoi.\ \AgdaField{MCParam.k} \B q\ .zoi.

\subsubsection{le me'oi .\AgdaKeyword{field}.\ pe le mu'oi glibau.\ symmetric cryptography .glibau.}
\paragraph{la'oi .\AgdaField{MCParam.ℓ}.}
ni'o la'o zoi.\ \AgdaField{MCParam.ℓ} \B q\ .zoi.\ ni clani pe'a fa la'o zoi.\ \AgdaField{MCParam.H} \B q \AgdaUnderscore\ .zoi.\

\paragraph{la'oi .\AgdaField{MCParam.H}.}
ni'o la'o zoi.\ \AgdaField{MCParam.H} \B q \B n\ .zoi.\ me'oi .hash.\ la'oi .\B{n}.

\paragraph{la'oi .\AgdaField{MCParam.σ₁}.}
ni'o la'o zoi.\ \AgdaField{MCParam.σ₁} \B q\ .zoi.\ me'oi .arbitrary.

\paragraph{la'oi .\AgdaField{MCParam.σ₂}.}
.i la'o zoi.\ \AgdaField{MCParam.σ₂} \B q\ .zoi.\ ji'a me'oi .arbitrary.

\paragraph{la'oi .\AgdaField{MCParam.G}.}
ni'o la'o zoi.\ \AgdaField{MCParam.G} \B q \B x\ .zoi.\ me'oi .pseudorandom.

\paragraph{lo ctaipe be lo su'u dubjavme'a ja co'e}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi bau la .lojban.\ fe la'oi .\AgdaField{n≤q}.\ ja la'oi .\AgdaField{t≥2}.\ ja la'oi .\AgdaField{ν≥μ}.\ ja la'oi .\AgdaField{ν≤μ+k}.\ ja la'oi .\AgdaField{σ₁≥m}.\ ja la'oi .\AgdaField{σ₂≥2*m}.\ ja la \AgdaField{ctejau}

\begin{code}
record MCParam : Set
  where
  field
    m : ℕ
    n : ℕ
    t : ℕ
  q : ℕ
  q = 2 ^ m
  field
    f : Vec (Fin 2) m
    F : Vec (Fin q) t
    ν : ℕ
    μ : ℕ
    ℓ : ℕ
    H : ℕ → Fin $ 2 ^ ℓ
    σ₁ : ℕ
    σ₂ : ℕ
    G : Fin $ 2 ^ ℓ → Fin $ 2 ^_ $ n + σ₂ * q + σ₁ * t + ℓ
  k : ℕ
  k = n ∸ m * t
  n-k : ℕ
  n-k = n ∸ k
  σ₂*q : ℕ
  σ₂*q = σ₂ * q
  σ₁*t : ℕ
  σ₁*t = σ₁ * t
  field
    n≤q : n ℕ.≤ q
    t≥2 : t ℕ.≥ 2
    ν≥μ : ν ℕ.≥ μ
    ν≤μ+k : ν ℕ.≤ μ + k
    σ₁≥m : σ₁ ℕ.≥ m
    σ₂≥2*m : σ₂ ℕ.≥ 2 * m
    ctejau : m * t ℕ.< n
\end{code}

\chap{la'oi .\F{Public}.}
ni'o la'au \chapsname\ li'u vasru le velcki be ko'a goi la'oi .\F{Public}.\ be'o je le pinka be ko'a be'o je le velcki be ko'a goi le fancu poi la'oi .\F{Public}.\ du lo ro se srana be ke'a ku'o be'o je le pinka be ko'a

\section{la'oi .\F{Public}.}
ni'o la'o zoi.\ \F{Public} \B q\ .zoi.\ se ctaipe lo gubni termifckiku pe la'oi .\B q.

\begin{code}
Public : MCParam → Set
Public p = 𝕄 (Fin 2) (MCParam.k p) $ MCParam.n-k p
\end{code}

\chap{la'oi .\AgdaRecord{Private}.\ je zo'e}
ni'o la'au \chapsname\ li'u vasru le velcki be ko'a goi la'oi .\AgdaRecord{Private}.\ ja zo'e be'o je le pinka be ko'a be'o je le velcki be ko'e goi le fancu poi ke'a srana vu'oi ko'a ja zo'e vu'o po'o ku'o be'o je le pinka be ko'e

\section{la'oi .\AgdaRecord{Private}.}
ni'o la'oi .\AgdaRecord{Private}.\ se ctaipe lo sivni termifckiku pe la'o glibau.\ Classic MCELIECE .glibau.

\subsection{le me'oi .\AgdaKeyword{field}.}

\paragraph{la'oi .\AgdaField{Private.lg}.}
ni'o la'o zoi.\ \AgdaField{Private.lg} \B p\ .zoi.\ nilzilcmi ja co'e la'o zoi.\ \AgdaField{Private.g} \B p\ .zoi.

\paragraph{la'oi .\AgdaField{Private.Γ}.}
ni'o la'o zoi.\ \AgdaField{Private.Γ} \B p\ .zoi.\ .orsi li re lo cpolinomi'a be fi la'o zoi.\ \AgdaField{Private.lg} \B p .zoi.\ bei fo ko'a goi la'o zoi.\ \D{Fin} \OpF \$ \AgdaField{Private.q} \B p\ .zoi.\ lo porsi be fi ko'a be'o poi la'o zoi.\ \AgdaField{Private.n} \B p\ .zoi.\ nilzilcmi ke'a

\paragraph{la'oi .\AgdaField{Private.s}.}
ni'o la'o zoi.\ \AgdaField{Private.s} \B p\ .zoi.\ porsi fi lo'i samsle je cu se nilzilcmi la'o zoi.\ \AgdaField{MCParam.n} \B p\ .zoi.

\begin{code}
record Private (p : MCParam) : Set
  where
  private
    q = MCParam.q p
    n = MCParam.n p
  field
    lg : ℕ
    Γ : Vec (Fin q) lg × Vec (Fin q) n
    s : Vec (Fin 2) n
  g = proj₁ Γ
\end{code}

\section{la'oi .\F{MatGen}.}
ni'o la'o zoi.\ \F{MatGen} \B x\ .zoi.\ du la'oi .\AgdaInductiveConstructor{nothing}.\ jonai cu me'oi .\AgdaInductiveConstructor{just}.\ lo gubni termifckiku poi ke'a mapti la'oi .\B x.

ni'o pilno le mu'oi glibau.\ semi-systematic form .glibau.\ ki'u le su'u ga je la .varik.\ cu djica lo nu mapti lo ro broda cei co'e gi tolmapti lo su'o broda fa le mu'oi glibau.\ systematic form .glibau.

\begin{code}
MatGen : {p : MCParam} → Private p → Maybe $ Public p
MatGen {p} _ = mapₘ toPus $ cyst $ repl H~
  where
  t = MCParam.t p
  n = MCParam.n p
  mf = 𝕄 (Fin $ MCParam.q p) t n
  mftwom = 𝕄 (Fin 2) (MCParam.m p * t) n
  -- | ni'o ro da zo'u da ctaipe la'oi .SemiSysForm.
  -- jo cu srana le mu'oi glibau. semi-systematic form
  -- .glibau.
  SemiSysForm : Set
  SemiSysForm = {!!}
  repl : mf → mftwom
  repl = mapᵥ {!!}
  cyst : mftwom → Maybe SemiSysForm
  cyst = {!!}
  toPus : SemiSysForm → Public p
  toPus = {!!}
  H~ : mf
  H~ = {!!}
\end{code}

\chap{la'oi .\F{KP}.\ je zo'e}

\section{la'oi .\F{KP}.}
ni'o la'o zoi.\ \F{KP} \B p\ .zoi.\ se ctaipe lo mu'oi glibau.\ Classic MCELIECE .glibau.\ mu'oi glibau.\ key pair .glibau.\ poi ke'a mapti la'oi .\B{p}.

.i ga naja la'oi .\B{t}.\ ctaipe la'o zoi.\ \F{KP}\ \AgdaUnderscore\ .zoi.\ gi cadga fa lo nu la'o zoi.\ \AgdaField{proj₂} \B t\ .zoi.\ sivni termifckiku je cu mapti la'oi .\B{t}.\ je la'o zoi.\ \AgdaField{proj₁} \B t\ .zoi.

\begin{code}
KP : MCParam → Set
KP p = Public p × Private p
\end{code}

\chap{le fancu poi tu'a ke'a filri'a tu'a lo termifckiku}
ni'o la'au \chapsname\ li'u vasru le velcki be vu'oi le fancu je zo'e vu'o poi tu'a ke'a filri'a lo nu ciksi lo termifckiku

\section{la'oi .\F{Irreducible}.}
ni'o \specimp{Irreducible}

\begin{code}
Irreducible : {p : MCParam}
            → Fin $ 2 ^ (MCParam.σ₁ p * MCParam.t p)
            → Maybe $ Vec (Fin $ MCParam.q p) $ MCParam.t p
Irreducible {p} d = fromList? g
  where
  t = MCParam.t p
  g = {!!}
\end{code}

\section{la'oi .\F{FieldOrdering}.}
ni'o \specimp{FieldOrdering}

\begin{code}
module FieldOrdering where
  toFin : {n : ℕ} → ℕ → Fin n
  toFin = {!!}

  α' : (p : MCParam)
     → let q = MCParam.q p in
       flip Vec q $ Fin (MCParam.σ₂ p) × Fin q
     → Vec (Fin q) q
  α' p = mapᵥ $ λ (a , π) → toFin $ sumᵥ $ mapᵥ (tefpi'i a π) $ allFin m
    where
    m = MCParam.m p
    -- | ni'o mo la .z.
    -- .i ga naja cpolynomi'a co'e gi na sarcu fa tu'a lo
    -- pilji  .i nibli la'e di'u fa le su'u ga je co'e gi
    -- pilno la'oi .Vec. tu'a lo cpolinomi'a  .i ku'i la
    -- .varik. na birti ko'a goi le du'u cpolinomi'a co'e
    -- .i ku'i cumki fa lo nu binxo  .i le su'u sampu cu
    -- krinu le su'u la .varik. cu milxe le ka ce'u senpi
    -- ko'a
    tefpi'i = λ a π j → toℕ π * {!!} ^ (m ∸ 1 ∸ toℕ j)

  module Sartre where
    -- | ni'o pilno la .jort. lo nu me'oi .lexicographic.
    -- porganzu
    jort : ∀ {a} → {A : Set a} → {m n : ℕ}
         → Op₁ $ flip Vec n $ Fin m × A
    jort {m = m} = mapᵥ proj₂ ∘ jort' ∘ mapᵥ (λ a → proj₁ a , a)
      where
      jort' : ∀ {a} → {A : Set a} → {n : ℕ}
            → Op₁ $ Vec (Fin m × A) n
      jort' = {!!}

    panci₂ : ∀ {a b} → {A : Set a} → {B : Set b} → {n : ℕ}
           → ⦃ Eq A ⦄
           → Vec (A × B) n
           → Maybe $ Vec (A × B) n
    panci₂ x = unzip x ▹ λ (x₁ , x₂) → mapₘ (flip zipᵥ x₂) $ panci x₁

    sartre : (p : MCParam)
           → let q = MCParam.q p in
             let vex = flip Vec q $ Fin (MCParam.σ₂ p) × Fin q in
             vex
           → Maybe vex
    sartre _ = mapₘ jort ∘ panci₂

  open Sartre
    using (
      sartre
    )

  FieldOrdering : {p : MCParam}
                → Fin $ MCParam.σ₂ p * MCParam.q p
                → Maybe $ Vec (Fin $ MCParam.q p) $ MCParam.q p
  FieldOrdering {p} f = mapₘ (α' p) $ sartre p $ indice a
    where
    q = MCParam.q p
    vex = flip Vec q $ Fin (MCParam.σ₂ p) × Fin q
    a : flip Vec q $ Fin $ MCParam.σ₂ p
    a = {!!}

open FieldOrdering
  using (
    FieldOrdering
  )
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{FieldOrdering}.\ mapti}

\begin{code}
module FieldOrderingVeritas where
  module ToFin where
    mleca : (m n : ℕ)
          → m ℕ.< suc n
          → toℕ (FieldOrdering.toFin {suc n} m) ≡ n
    mleca = {!!}

    dubjavmau : (m n : ℕ)
              → ¬_ $ m ℕ.< suc n
              → toℕ (FieldOrdering.toFin {suc n} m) ≡ {!!}
    dubjavmau = {!!}

  module Sartre where
    module Jort where
      dubjavme'a : ∀ {a} → {A : Set a} → {m n : ℕ}
                 → (v : Vec (Fin m × A) $ suc n)
                 → (i : Fin n)
                 → let v' = FieldOrdering.Sartre.jort v in
                   let i' = 𝔽.inject₁ i in
                   ((𝕊._≤_ on (show ∘ proj₁ ∘ lookup v'))
                     i'
                     (suc i))
      dubjavme'a = {!!}

      cmimajos : ∀ {a} → {A : Set a} → {m n : ℕ}
               → (v : Vec (Fin m × A) n)
               → (i : Fin n)
               → let v' = FieldOrdering.Sartre.jort v in
                 ∃ $ λ i' → lookup v i ≡ lookup v' i'
      cmimajos = {!!}

    module Panci₂ where
      nada : ∀ {a b} → {A : Set a} → {B : Set b} → {n : ℕ}
           → ⦃ _ : Eq A ⦄
           → (x : Vec (A × B) n)
           → (n₁ n₂ : Fin n)
           → lookup x n₁ ≡ lookup x n₂
           → ¬_ $ n₁ ≡ n₂
           → FieldOrdering.Sartre.panci₂ x ≡ nothing
      nada = {!!}

      jus : ∀ {a b} → {A : Set a} → {B : Set b} → {n : ℕ}
          → ⦃ _ : Eq A ⦄
          → (x : Vec (A × B) n)
          → (_ : (n₁ n₂ : Fin n)
               → lookup x n₁ ≡ lookup x n₂
               → n₁ ≡ n₂)
          → FieldOrdering.Sartre.panci₂ x ≡ just x
      jus = {!!}

    nada : (p : MCParam)
         → (x : _)
         → (n₁ n₂ : Fin _)
         → lookup x n₁ ≡ lookup x n₂
         → ¬_ $ n₁ ≡ n₂
         → FieldOrdering.Sartre.sartre p x ≡ nothing
    nada = {!!}
\end{code}

\section{la'oi .\F{FixedWeight}.}
ni'o \specimp{FixedWeight}

ni'o \termineidyr{FixedWeight}

\begin{code}
module FixedWeight where
  τ' : MCParam → ℕ
  τ' p = if MCParam.n p ≡ᵇ MCParam.q p then MCParam.t p else {!!}

  d : (p : MCParam)
    → Fin $ 2 ^_ $ MCParam.σ₁ p * τ' p
    → Vec ℕ $ τ' p
  d p b = mapᵥ (λ j → sumᵥ $ mapᵥ (uijis j) $ allFin _) $ allFin $ τ' p
    where
    uijis : Fin $ τ' p → Fin $ MCParam.m p → ℕ
    uijis j i = 2 ^ toℕ i * toℕ (lookup b' ind)
      where
      ind = f2f mind ▹_ $ coerce $ cong Fin $ proj₂ sukdiz
        where
        -- | ni'o zo .mind. cmavlaka'i lu mabla
        -- .indice li'u
        --
        -- ni'o ma zmadu fi le ka ce'u zabna kei fe
        -- le me'oi .fromℕ. co'e noi ke'a pluja je cu
        -- fegli la .varik.
        -- .i ga naja mleca ko'a goi
        -- la'o zoi. MCParam.σ₁ * τ' p .zoi. gi frili cumki
        -- fa tu'a la'oi .fromℕ.  .i ku'i xu mleca ko'a
        mind = fromℕ $ toℕ i + MCParam.σ₁ p * toℕ j
        sukdiz : ∃ $ λ n → suc n ≡ MCParam.σ₁ p * τ' p
        sukdiz = sukdiz-¬0 (MCParam.σ₁ p) (τ' p) {!!} {!!}
          where
          sukdiz-¬0 : (m n : ℕ)
                    → ¬ (m ≡ 0)
                    → ¬ (n ≡ 0)
                    → ∃ $ λ o → suc o ≡ m * n
          sukdiz-¬0 0 n N₁ N₂ = refl ⇒⇐ N₁
          sukdiz-¬0 m 0 N₁ N₂ = refl ⇒⇐ N₂
          sukdiz-¬0 (suc m) (suc n) N₁ N₂ = {!!}
      b' = nbits $ toℕ b

  a? : (p : MCParam)
     → Fin $ 2 ^_ $ MCParam.σ₁ p * τ' p
     → Maybe $ Vec (Fin $ MCParam.n p) $ MCParam.t p
  a? p b = _>>=ₘ panci $ toVec? $ 𝕃.take (MCParam.t p) mlen
    where
    -- | ni'o zo .mlen. cmavlaka'i lu mleca la .n. li'u
    mlen : List $ Fin $ MCParam.n p
    mlen = 𝕃.mapMaybe id $ mapₗ mlen? $ toList $ d p b
      where
      mlen? = mapₘ fromℕ< ∘ decToMaybe ∘ (ℕ._<? _)

  FixedWeight' : (p : MCParam)
               → Fin $ 2 ^_ $ MCParam.σ₁ p * τ' p
               → Maybe $ ∃ $ λ e → hWV𝔽 e ≡ MCParam.t p
  FixedWeight' p b = mapₘ (map₂ proj₁ ∘ e') $ a? p b
    where
    e' : (a : _)
       → Σ (Vec (Fin 2) (MCParam.n p)) $ λ e
         → hWV𝔽 e ≡ MCParam.t p
         × let el = 𝕃.allFin _ in
           flip Listal.All el $ (suc zero ≡_) ∘ lookup e ∘ lookup a
    e' = {!!}

  {-# NON_TERMINATING #-}
  FixedWeight : {p : MCParam}
              → (IO $ Σ
                  (Vec (Fin 2) $ MCParam.n p)
                  ((_≡ MCParam.t p) ∘ hWV𝔽))
  FixedWeight {p} = cof IO.>>= restart? ∘ FixedWeight' p
    where
    OT = ∃ $ λ e → hWV𝔽 e ≡ MCParam.t p
    -- | ni'o cumki fa lo nu cumki fa lo nu tu'a
    -- la'oi .restart?. rinka lo nu na me'oi .terminate.
    restart? : Maybe OT → IO OT
    restart? = maybe pure $ FixedWeight {p}
    -- | ni'o la'o zoi. mceliece.pdf .zoi. vasru le na'e
    -- zabna je velcki be la'oi .τ'.  .i la .varik.
    -- na birti lo du'u pilji ji kau cu tenfa  .i ku'i la
    -- .varik. cu djuno le du'u na mapti fa le me zo joi se
    -- xamsku
    cof = cunsof {MCParam.σ₁ p * τ' p}

open FixedWeight
  using (
    FixedWeight
  )
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{FixedWeight}.\ mapti}

\begin{code}
module FixedWeightVeritas where
  open FixedWeight

  module τ' where
    dun : (p : MCParam)
        → MCParam.n p ≡ MCParam.q p
        → τ' p ≡ MCParam.t p
    dun p d = begin
      τ' p ≡⟨ {!!} ⟩
      MCParam.t p ∎
      where
      open ≡-Reasoning

    nth : (p : MCParam)
        → (i : ℕ)
        → let q = MCParam.q p in
          let n = MCParam.n p in
          let 2^i = ℕ.suc $ proj₁ $ pausyk 2 i in
          q div 2^i ℕ.≤ n
        → n ℕ.≤ q div 2^i
        → τ' p ≡ (2 ^ i) * MCParam.t p
    nth = {!!}
\end{code}

\section{la'oi .\F{Encap}.}
ni'o \specimp{Encap}

\begin{code}
Encap : {p : MCParam}
      → let F = Fin $ 2 ^ MCParam.ℓ p in
        IO $ Vec (Fin 2) (MCParam.n-k p) × F × F
Encap {p} = uncurry (Encap' {p}) IO.<$> FixedWeight {p}
  where
  Encap' : {p : MCParam}
         → (e : Vec (Fin 2) $ MCParam.n p)
         → hWV𝔽 e ≡ MCParam.t p
         → let F = Fin $ 2 ^ MCParam.ℓ p in
           Vec (Fin 2) (MCParam.n-k p) × F × F
  Encap' = {!!}
\end{code}

\section{la'oi .\F{SeededKeyGen}.}
ni'o \specimp{SeededKeyGen}

.i la'o zoi.\ \F{SeededKeyGen} \B p \B δ\ .zoi.\ .orsi li re ko'a goi lo mu'oi glibau.\ Classic MCELIECE .glibau.\ ke sivni termifckiku lo mapti be ko'a

ni'o me'oi .recurse.  .i \termineidyr{SeededKeyGen}

\begin{code}
module SeededKeyGen where
  Eₚ' : {p : MCParam}
      → Fin $ 2 ^ MCParam.ℓ p
      → Fin $ 2 ^ MCParam.σ₁*t p
  Eₚ' {p} = b2f ∘ drop n ∘ nbits {n + MCParam.σ₁*t p} ∘ toℕ
    where
    n = MCParam.n p

  module G? where
    frir : (p : MCParam)
         → Vec (Fin $ MCParam.q p) $ MCParam.t p
         → let Vq = Vec $ Fin $ MCParam.q p in
           Vq (MCParam.n p) × ∃ Vq
    frir _ g = {!!} , _ , g

    g? : {p : MCParam}
       → Fin $ 2 ^ MCParam.ℓ p
       → let n = MCParam.n p in
         let Vq = Vec $ Fin $ MCParam.q p in
         Maybe $ Vq n × ∃ Vq
    g? {p} = mapₘ (frir p) ∘ Irreducible {p} ∘ Eₚ' {p}

  open G?
    using (
      g?
    )

  module Sivni?I where
    f : {p : MCParam}
      → Fin $ 2 ^ MCParam.ℓ p
      → let Vq = Vec $ Fin $ MCParam.q p in
        Vq (MCParam.n p) × ∃ Vq
      → Private p
    f {p} δ (j , lg , g) = record {
      lg = lg;
      Γ = g , j;
      s = nbits $ toℕ $ b2f $ nbits {MCParam.n p} $ toℕ δ
      }

  sivni? : {p : MCParam}
         → Fin $ 2 ^ MCParam.ℓ p
         → Maybe $ Private p
  sivni? {p} δ = mapₘ (Sivni?I.f δ) $ g? {p} δ

  mapti? : {p : MCParam}
         → Fin $ 2 ^ MCParam.ℓ p
         → (Fin
             (_^_
               2
               (MCParam.n p +
                MCParam.σ₂*q p +
                MCParam.σ₁*t p +
                MCParam.ℓ p)))
         → Maybe $ KP p
  mapti? {p} δ E = _,ₘ_ (sivni >>=ₘ MatGen) sivni
    where
    sivni = sivni? {p} δ
    _,ₘ_ = (apₘ ∘₂ mapₘ) _,_

  δ'f : (p : MCParam) → Op₁ $ Fin $ 2 ^ MCParam.ℓ p
  δ'f p δ = b2f $ reverseᵥ $ nbits {MCParam.ℓ p} $ toℕ $ rev E
    where
    E = MCParam.G p δ
    rev : {n : ℕ} → Op₁ $ Fin n
    rev = opposite

    module Veritas where
      zivle : {n : ℕ} → (t : Fin n) → t ≡ rev (rev t)
      zivle = {!!}

  {-# NON_TERMINATING #-}
  SeededKeyGen : {p : MCParam} → Fin $ 2 ^ MCParam.ℓ p → KP p
  SeededKeyGen {p} δ = fromMaybe (SeededKeyGen δ') $ mapti? δ E
    where
    E = MCParam.G p δ
    δ' = δ'f p δ

open SeededKeyGen
  using (
    SeededKeyGen
  )
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{SeededKeyGen}.\ mapti}

\begin{code}
module SeededKeyGenVeritas where
  open SeededKeyGen

  module Eₚ' where
    nos : {p : MCParam}
        → let Z = mink zero ∘ proj₂ ∘ pausyk 1 in
          (_≡_
            (Eₚ' {p} $ Z $ MCParam.ℓ p)
            (Z $ MCParam.σ₁*t p))
    nos {p} = begin
      Eₚ' {p} (Z ℓ) ≡⟨ refl ⟩
      b2f (drop n $ nb $ toℕ $ Z $ MCParam.ℓ p) ≡⟨ refl ⟩
      _ ≡⟨ tomindus _ (P ℓ) ▹ sym ▹ cong (b2f ∘ drop n ∘ nb) ⟩
      b2f (drop n $ nb 0) ≡⟨ refl ⟩
      _ ≡⟨ NbitsVeritas.zeros {n + σ₁*t} ▹ cong (b2f ∘ drop n) ⟩
      b2f (drop n $ replicate {n = n + σ₁*t} zero) ≡⟨ refl ⟩
      _ ≡⟨ replidrop {m = n} {σ₁*t} zero ▹ cong b2f ⟩
      b2f (replicate {n = σ₁*t} zero) ≡⟨ B2fVeritas.non' 1 $ σ₁*t ⟩
      Z (MCParam.σ₁*t p) ∎
      where
      P = proj₂ ∘ pausyk 1
      Z = mink zero ∘ P
      σ₁*t = MCParam.σ₁*t p
      ℓ = MCParam.ℓ p
      n = MCParam.n p
      nb = nbits {n + σ₁*t}
      open ≡-Reasoning
      replidrop : ∀ {a} → {A : Set a} → {m n : ℕ}
                → (x : A)
                → (_≡_
                    (drop m $ replicate {n = m + n} x)
                    (replicate x))
      replidrop {m = m} {n = n} x = begin
        drop m (replicate {n = m + n} x) ≡⟨ {!!} ⟩
        (fromList (𝕃.drop m $ 𝕃.replicate (m + n) x) ▹ coerce k) ≡⟨ {!!} ⟩
        (fromList (𝕃.replicate n x) ▹ coerce k') ≡⟨ {!!} ⟩
        replicate {n = n} x ≡⟨ refl ⟩
        replicate x ∎
        where
        k' = DLP.length-replicate _ ▹ cong (Vec _)
        k = cong (Vec _) $ begin
          𝕃.length (𝕃.drop m $ 𝕃.replicate (m + n) x) ≡⟨ refl ⟩
          _ ≡⟨ m↓r[m+n]≡r[n] m n x ▹ cong 𝕃.length ⟩
          𝕃.length (𝕃.replicate n x) ≡⟨ DLP.length-replicate n ⟩
          n ∎
          where
          m↓r[m+n]≡r[n] : ∀ {a} → {A : Set a}
                        → (m n : ℕ)
                        → (x : A)
                        → (_≡_
                            (𝕃.drop m $ 𝕃.replicate (m + n) x)
                            (𝕃.replicate n x))
          m↓r[m+n]≡r[n] 0 _ _ = refl
          m↓r[m+n]≡r[n] (ℕ.suc m) = m↓r[m+n]≡r[n] m

  module G?V where
    open SeededKeyGen.G?

    nada : {p : MCParam}
         → (δ : Fin $ 2 ^ MCParam.ℓ p)
         → let Eₚ = Eₚ' {p} δ in
           Irreducible {p} Eₚ ≡ nothing
         → G?.g? {p} δ ≡ nothing
    nada {p} δ d = begin
      G?.g? {p} δ ≡⟨ refl ⟩
      mapₘ (frir p) (Irreducible {p} $ Eₚ' {p} δ) ≡⟨ refl ⟩
      mapₘ (frir p) irep ≡⟨ d ▹ cong (mapₘ $ frir p) ⟩
      mapₘ (frir p) nothing ≡⟨ refl ⟩
      nothing ∎
      where
      irep = Irreducible {p} $ Eₚ' {p} δ
      open ≡-Reasoning

    ir₃ : {p : MCParam}
        → (δ : Fin $ 2 ^ MCParam.ℓ p)
        → let Eₚ = Eₚ' {p} δ in
          (_≡_
            (mapₘ (_ ,_) $ Irreducible {p} Eₚ)
            (mapₘ proj₂ $ g? {p} δ))
    ir₃ {p} δ with Irreducible {p} $ Eₚ' {p} δ
    ... | just _ = refl
    ... | nothing = refl

  module Sivni? where
    sles : {p : MCParam}
         → (δ : Fin $ 2 ^ MCParam.ℓ p)
         → toℕ δ ℕ.< 2 ^ MCParam.n p
         → (_∈_
             (mapₘ (toℕ ∘ b2f ∘ Private.s) $ sivni? {p} δ)
             (nothing ∷ just (toℕ δ) ∷ List.[]))
    sles {p} δ m with sivni? {p} δ
    ... | nothing = refl
    ... | just S = subst (_∈ L) (dun ▹ cong just) just∈L
      where
      L = nothing ∷ just (toℕ δ) ∷ List.[]
      dun : toℕ δ ≡ toℕ (b2f $ Private.s S)
      dun = sym $ begin
        toℕ (b2f $ Private.s S) ≡⟨ {!!} ⟩
        toℕ δ ∎
        where
        open ≡-Reasoning
      just∈L : just (toℕ δ) ∈ L
      just∈L = ∃⇒∈ {x = L} $ suc zero , refl
        where
        ∃⇒∈ : ∀ {a} → {A : Set a}
            → ⦃ _ : Eq A ⦄
            → {x : List A}
            → {e : A}
            → ∃ $ (_≡ e) ∘ 𝕃.lookup x
            → e ∈ x
        ∃⇒∈ {x = x ∷ xs} {e} (𝔽.zero , d) = sym $ begin
          length (𝕃.take 1 $ 𝕃.filter (e ≟_) $ x ∷ tf xs) ≡⟨ {!!} ⟩
          𝕃.length (x ∷ []) ≡⟨ refl ⟩
          1 ∎
          where
          open ≡-Reasoning
          tf = toList ∘ fromList
        ∃⇒∈ {x = x ∷ xs} {e} (𝔽.suc n , d) = {!!}

    nog : {p : MCParam}
        → (δ : Fin $ 2 ^ MCParam.ℓ p)
        → G?.g? {p} δ ≡ nothing
        → sivni? {p} δ ≡ nothing
    nog {p} δ d = begin
      sivni? {p} δ ≡⟨ refl ⟩
      mapₘ (Sivni?I.f δ) (G?.g? {p} δ) ≡⟨ refl ⟩
      _ ≡⟨ d ▹ cong (mapₘ $ Sivni?I.f δ) ⟩
      mapₘ (Sivni?I.f δ) nothing ≡⟨ refl ⟩
      nothing ∎
      where
      open ≡-Reasoning

    no,ir : {p : MCParam}
          → (δ : Fin $ 2 ^ MCParam.ℓ p)
          → Irreducible {p} (Eₚ' {p} δ) ≡ nothing
          → sivni? {p} δ ≡ nothing
    no,ir {p} δ d = begin
      sivni? {p} δ ≡⟨ refl ⟩
      mapₘ (Sivni?I.f δ) (G?.g? {p} δ) ≡⟨ refl ⟩
      S (G?.g? {p} δ) ≡⟨ refl ⟩
      S (mapₘ (G?.frir p) $ Irreducible {p} $ Eₚ' {p} δ) ≡⟨ refl ⟩
      _ ≡⟨ d ▹ cong (S ∘ mapₘ (G?.frir p)) ⟩
      S (mapₘ (G?.frir p) nothing) ≡⟨ refl ⟩
      S nothing ≡⟨ refl ⟩
      nothing ∎
      where
      open ≡-Reasoning
      S = mapₘ $ Sivni?I.f δ

  module Mapti? where
    nos : {p : MCParam}
        → (δ : Fin $ 2 ^ MCParam.ℓ p)
        → (E : _)
        → sivni? {p} δ ≡ nothing
        → mapti? {p} δ E ≡ nothing
    nos {p} δ E d = begin
      mapti? δ E ≡⟨ refl ⟩
      _,ₘ_ (sivni? {p} δ >>=ₘ MatGen) (sivni? {p} δ) ≡⟨ refl ⟩
      (λ x → _,ₘ_ (x >>=ₘ MatGen) x) (sivni? {p} δ) ≡⟨ refl ⟩
      _ ≡⟨ d ▹ cong (λ x → _,ₘ_ (x >>=ₘ MatGen) x) ⟩
      (λ x → _,ₘ_ (x >>=ₘ MatGen) x) nothing ≡⟨ refl ⟩
      nothing ∎
      where
      open ≡-Reasoning
      _,ₘ_ = (apₘ ∘₂ mapₘ) _,_

    jus : {p : MCParam}
        → (δ : Fin $ 2 ^ MCParam.ℓ p)
        → (E : _)
        → Set {!!} ∋ {!!}
        → mapti? {p} δ E ≡ just {!!}
    jus = {!!}
\end{code}

\section{la'oi .\F{KeyGen}.}
ni'o la'o zoi.\ \F{KeyGen} \B p\ .zoi.\ me'oi .\F{pure}.\ lo me'oi .pseudorandom.\ poi ke'a .orsi li re ko'a goi lo mu'oi glibau.\ Classic MCELIECE .glibau.\ ke sivni termifckiku lo mapti be ko'a

\begin{code}
KeyGen : (p : MCParam) → IO $ KP p
KeyGen p = SeededKeyGen IO.<$> cunsof {n = MCParam.ℓ p}
\end{code}

\chap{le fancu poi tu'a ke'a filri'a lo nu me'oi .encode.\ kei je lo nu me'oi .decode.}
ni'o ko'a goi la'au \chapsname\ li'u vasru le velcki be ko'e goi vu'oi le fancu poi tu'a ke'a filri'a lo nu me'oi .encode.\ ku'o je le fancu poi tu'a ke'a filri'a lo nu me'oi .decode.\ ge'u je le pinka be ko'e\sds  .i la .varik.\ na birti lo du'u xu kau sarcu fa lo nu me'oi .abstract.\ ko'a

\section{la'oi .\F{Hx}.}
ni'o la'o zoi.\ \F{Hx} \B p \B T\ .zoi.\ konkatena lo dunli nacmeimei la'oi .\B{T}.

\begin{code}
module Hx where
  n∸k+k≡n : (p : MCParam)
          → MCParam.n-k p + MCParam.k p ≡ MCParam.n p
  n∸k+k≡n p = DNP.m∸n+n≡m $ DNP.m∸n≤m _ $ m * _
    where
    m = MCParam.m p

  Hx : (p : MCParam)
     → Public p
     → 𝕄 (Fin 2) (MCParam.n p) $ MCParam.n-k p
  Hx p T = I zero (suc zero) ∣ T ▹ coerce n∸k+k≡n'
    where
    n∸k+k≡n' = n∸k+k≡n p ▹ cong nacmeimid
      where
      nacmeimid = λ i → 𝕄 (Fin 2) i $ MCParam.n-k p

open Hx
  using (
    Hx
  )
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{Hx}.\ mapti}

\begin{code}
module HxVeritas where
  kunti₁ : (p : MCParam)
         → (T : Public p)
         → (d : MCParam.n p ≡ 0)
         → let []' = [] ▹_ $ coerce $ d ▹ sym ▹ cong (Vec _) in
           Hx p T ≡ replicate []'
  kunti₁ = {!!}

  pavind : (p : MCParam)
         → (T : Public p)
         → (m : Fin _)
         → (n : Fin _)
         → toℕ m ≡ toℕ n
         → lookup (lookup (Hx p T) m) n ≡ suc zero
  pavind p T m n d = begin
    lookup (lookup (Hx p T) m) n ≡⟨ {!!} ⟩
    lookup (lookup (I zero $ suc zero) m) m ≡⟨ {!!} ⟩
    suc zero ∎
    where
    open ≡-Reasoning
\end{code}

\section{la'oi .\F{Encode}.}
ni'o \specimp{Encode}

\begin{code}
Encode : (p : MCParam)
       → (e : Vec (Fin 2) $ MCParam.n p)
       → Public p
       → hWV𝔽 e ≡ MCParam.t p
       → Vec (Fin 2) $ MCParam.n-k p
Encode p e T refl = flip moult e $ Hx p T
\end{code}

\subsection{le krinu be tu'a lo dunli ctaipe}
ni'o co'e lo ctaipe be lo su'u dunli kei ki'u le su'u ga je co'e gi .indika le du'u sarcu fa lo nu dunli kei kei fa tu'a le pagbu be la'o zoi.\ \texttt{mceliece.pdf}\ .zoi.\ be'o pe la'oi .\algoritma{Decode}.

\section{la'oi .\F{Decode}.}
ni'o \specimp{Decode}\sds  .i la'oi .\F{Decode}.\ na prane pe'a le ka fanva ko'a fu ce'u

\begin{code}
module Decode where
  xv : MCParam → (MCParam → ℕ) → Set
  xv = Vec (Fin 2) ∘₂ flip _$_

  mapti : {p : MCParam}
        → xv p MCParam.n-k
        → Public p
        → xv p MCParam.n
        → Set
  mapti {p} C₀ bar e = ∃ $ _≡_ C₀ ∘ Encode p e bar

  mapti? : {p : MCParam}
         → (C₀ : xv p MCParam.n-k)
         → (bar : Public p)
         → xv p MCParam.n
         → Maybe $ ∃ $ mapti {p} C₀ bar
  mapti? C₀ bar e = mapₘ (e ,_) ctaiporsis
    where
    ctaiporsis = dun? >>=ₘ λ x → mapₘ (x ,_) dun?

  module V' where
    n∸k+k≡n : (p : MCParam)
            → (_≡_
                (xv p $ λ p → MCParam.n-k p + MCParam.k p)
                (xv p MCParam.n))
    n∸k+k≡n p = DNP.m∸n+n≡m k≤n ▹ cong (Vec _)
      where
      k≤n = DNP.m∸n≤m _ $ MCParam.m p * MCParam.t p

    v' : (p : MCParam) → xv p MCParam.n-k → xv p MCParam.n
    v' p C₀ = C₀ ++ replicate zero ▹_ $ coerce $ n∸k+k≡n p

  open V'
    using (
      v'
    )

  module C' where
    c' : {p : MCParam}
       → (C₀ : xv p MCParam.n-k)
       → let v = v' p C₀ in
         Maybe $ ∃ $ λ c → dist c v refl ℕ.≤ MCParam.t p
    c' = {!!}

  open C'
    using (
      c'
    )

  Decode : {p : MCParam}
         → Vec (Fin 2) $ MCParam.n-k p
         → Public p
         → ∃ $ Vec $ Fin $ MCParam.q p
         → Vec (Fin $ MCParam.q p) $ MCParam.n p
         → Maybe $ Vec (Fin 2) $ MCParam.n p
  Decode {p} C₀ bar (_ , g) α' = e >>=ₘ mapₘ proj₁ ∘ mapti?' C₀ bar
    where
    mapti?' = mapti? {p}
    e = flip mapₘ c $ zipWithᵥ (f𝔽 _+_) v
      where
      v = v' p C₀
      c = mapₘ proj₁ $ c' {p} C₀

open Decode
  using (
    Decode
  )
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{Decode}.\ mapti}

\begin{code}
module DecodeVeritas where
  open Decode
    hiding (
      module V'
    )

  module Mapti? where
    jus : {p : MCParam}
        → (C₀ : xv p MCParam.n-k)
        → (bar : Public p)
        → (e : xv p MCParam.n)
        → mapti {p} C₀ bar e
        → ∃ $ (mapti? {p} C₀ bar e ≡_) ∘ just
    jus {p} C₀ bar e m = _ , dunlyctaipe
      where
      open ≡-Reasoning
      dunlyctaipe = begin
        mapti? {p} C₀ bar e ≡⟨ refl ⟩
        mapₘ (e ,_) (dun? >>=ₘ λ x → dun? ▹ mapₘ (x ,_)) ≡⟨ refl ⟩
        _ ≡⟨ xys m₁ ▹ cong (λ j → mapₘ (e ,_) $ j >>=ₘ λ x → dun? ▹ mapₘ (x ,_)) ⟩
        mapₘ (e ,_) (just m₁ >>=ₘ λ x → dun? ▹ mapₘ (x ,_)) ≡⟨ refl ⟩
        mapₘ (e ,_) (mapₘ (m₁ ,_) dun?) ≡⟨ refl ⟩
        _ ≡⟨ DMP.map-compose {g = e ,_} {m₁ ,_} dun? ▹ sym ⟩
        mapₘ (λ i → e , m₁ , i) dun? ≡⟨ xys m₂ ▹ cong (mapₘ _) ⟩
        mapₘ (λ i → e , m₁ , i) (just m₂) ≡⟨ refl ⟩
        just (e , m₁ , m₂) ∎
        where
        m₁ = proj₁ m
        m₂ = proj₂ m
        xys = Dun?Veritas.jus

    nada : {p : MCParam}
         → (C₀ : xv p MCParam.n-k)
         → (bar : Public p)
         → (e : xv p MCParam.n)
         → ¬_ $ mapti {p} C₀ bar e
         → mapti? {p} C₀ bar e ≡ nothing
    nada C₀ bar e N = begin
      mapti? C₀ bar e ≡⟨ refl ⟩
      mapₘ (e ,_) (dun? >>=ₘ λ x → mapₘ (x ,_) dun?) ≡⟨ {!!} ⟩
      nothing ∎
      where
      open ≡-Reasoning

    xor : {p : MCParam}
        → (C₀ : xv p MCParam.n-k)
        → (bar : Public p)
        → (e : xv p MCParam.n)
        → (_∈_
            (mapₘ proj₁ $ mapti? {p} C₀ bar e)
            (just e ∷ nothing ∷ List.[]))
    xor = {!!}

  module V' where
    open Decode.V'

    vc' : {p : MCParam}
       → xv p MCParam.n-k
       → xv p $ λ p → MCParam.n-k p + MCParam.k p
    vc' {p} C₀ = v' p C₀ ▹_ $ coerce $ n∸k+k≡n p ▹ sym

    vc≡C₀++rz : {p : MCParam}
              → (C₀ : xv p MCParam.n-k)
              → let vc = vc' {p} C₀ in
                vc ≡ C₀ ++ replicate zero
    vc≡C₀++rz {p} C₀ = CoerceVeritas.flipko _ (n∸k+k≡n p) ▹ sym


    pamois : {p : MCParam}
           → (C₀ : xv p MCParam.n-k)
           → let vc = vc' {p} C₀ in
             take (length C₀) vc ≡ C₀
    pamois {p} C₀ = begin
      take (length C₀) vc ≡⟨ vc≡C₀++rz {p} C₀ ▹_ $ cong $ take _ ⟩
      take (length C₀) (C₀ ++ replicate zero) ≡⟨ takedun C₀ _ ⟩
      C₀ ∎
      where
      vc = vc' {p} C₀
      takedun : ∀ {a} → {A : Set a} → {m n : ℕ}
              → (x : Vec A m)
              → (z : Vec A n)
              → take m (x ++ z) ≡ x
      takedun [] z = refl
      takedun {m = suc m} x@(x₁ ∷ xs) [] = begin
        take (suc m) (x ++ []) ≡⟨ {!!} ⟩
        take (suc m) x' ≡⟨ {!!} ⟩
        x ∎
        where
        open ≡-Reasoning
        x' : Vec _ $ suc m + 0
        x' = x ▹_ $ coerce $ DNP.+-identityʳ _ ▹ sym ▹ cong (Vec _)
      takedun (x ∷ xs) (z ∷ zs) = takedun xs (z ∷ zs) ▹ {!!}
      open ≡-Reasoning

    romois : {p : MCParam}
           → (C₀ : xv p MCParam.n-k)
           → let vc = vc' {p} C₀ in
             replicate zero ≡ drop (length C₀) vc 
    romois {p} C₀ = sym $ begin
      drop (length C₀) vc ≡⟨ vc≡C₀++rz {p} C₀ ▹ cong (drop _) ⟩
      drop (length C₀) (C₀ ++ replicate zero) ≡⟨ dropdun C₀ _ ⟩
      replicate zero ∎
      where
      vc = vc' {p} C₀
      dropdun : ∀ {a} → {A : Set a} → {m n : ℕ}
              → (x : Vec A m)
              → (z : Vec A n)
              → drop m (x ++ z) ≡ z
      dropdun [] _ = refl
      dropdun (x ∷ xs) z = dropdun xs z ▹ coerce (cong (_≡ z) {!!})
      open ≡-Reasoning
\end{code}

\section{le su'u la'oi .\F{Decode}.\ srana la'oi .\F{Encode}.}

\begin{code}
module DecodeEncode where
  Decode∘Encode : {p : MCParam}
                → (e : Vec (Fin 2) $ MCParam.n p)
                → (g : Public p)
                → (dun : hWV𝔽 e ≡ MCParam.t p)
                → (_≡_
                    (just e)
                    (Decode
                      {p}
                      -- | .i ba xruti
                      (Encode p e g dun)
                      g
                      {!!}
                      {!!}))
  Decode∘Encode = {!!}
\end{code}
\end{document}
