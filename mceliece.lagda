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
\newunicodechar{∨}{\ensuremath{\mathnormal\vee}}
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{∶}{\ensuremath{\mathnormal\colon\!\!}}
\newunicodechar{ℙ}{\ensuremath{\mathbb{P}}}
\newunicodechar{𝔽}{\ensuremath{\mathbb{F}}}
\newunicodechar{𝕄}{\ensuremath{\mathbb{M}}}
\newunicodechar{𝔹}{\ensuremath{\mathbb{B}}}
\newunicodechar{ν}{\ensuremath{\nu}}
\newunicodechar{μ}{\ensuremath{\mu}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{^\mathrm{b}}}
\newunicodechar{≥}{\ensuremath{\mathnormal{\geq}}}
\newunicodechar{ϕ}{\ensuremath{\mathnormal{\phi}}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\wedge}}}
\newunicodechar{∣}{\ensuremath{\mathnormal{|}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\forall}}
\newunicodechar{ℓ}{\ensuremath{\ell}}
\newunicodechar{σ}{\ensuremath{\sigma}}
\newunicodechar{α}{\ensuremath{\alpha}}
\newunicodechar{₁}{\ensuremath{_1}}
\newunicodechar{₂}{\ensuremath{_2}}
\newunicodechar{ᵥ}{\ensuremath{_\mathsf{v}}}
\newunicodechar{ₘ}{\ensuremath{_\mathsf{m}}}
\newunicodechar{≤}{\ensuremath{\mathnormal{\leq}}}
\newunicodechar{⍉}{\ensuremath{∘\hspace{-0.455em}\backslash}}
\newunicodechar{₀}{\ensuremath{\mathnormal{_0}}}
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}
\newunicodechar{δ}{\ensuremath{\mathnormal{\delta}}}

\newcommand\hashish{cbf1 42fe 1ebd b0b2 87a4 4018 340b 8159 7ef1 3a63 6f5d 76f4 6f48 a080 b2bc d3f1 3922 f0f1 5219 94cc 5e71 fb1f b2d9 d9f8 dd3b ffe6 be32 0056 5cca 21c4 28eb 9de1}

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

\chapter{le terfi'i ja co'e}
ni'o ko'a goi la'au le me'oi .Agda.\ me'oi .implementation.\ be la'o glibau.\ Classic MCELIECE .glibau.\ li'u me'oi .Agda.\ co'e  .i tu'a ko'a cu filri'a lo nu jimpe le mu'oi glibau.\ Classic MCELIECE .glibau.

.i la .varik.\ cu mutce le ka ce'u troci lo nu ko'a drani je cu zabna fi la .varik.\ldots kei je nai lo nu ko'a mutce le ka ce'u sutra  .i ku'i la .varik.\ cu na tolnei lo nu da'i ko'a drani ba'e je cu sutra

\chapter{le me'oi .preamble.}
ni'o la'au le me'oi .preamble.\ li'u vasru le .importe ja me'oi .pragma.\ selsku

\begin{code}
{-# OPTIONS --guardedness #-}

open import IO
open import Data.Fin
  renaming (
    _+_ to _+F_
  )
open import Data.Vec
  renaming (
    map to mapᵥ;
    sum to sumᵥ;
    foldr to foldrᵥ;
    zipWith to zipWithᵥ;
    zip to zipᵥ;
    reverse to reverseᵥ;
    transpose to ⍉
  )
open import Function
open import Data.Bool
  hiding (
    T
  )
open import Data.List
  using (
    _∷_;
    List;
    map;
    reverse;
    []
  )
  renaming (
    take to takeₗ
  )
open import Data.Digit
  using (
    toNatDigits
  )
open import Data.Maybe
  renaming (
    map to mapₘ
  )
open import Data.These
  using (
    These;
    this;
    that;
    these
  )
open import Algebra.Core
open import Data.Product
open import Data.Nat as ℕ
open import Data.Nat.DivMod
open import Data.Vec.Bounded
  using (
    Vec≤
  )
open import Algebra.Structures
open import Data.Nat.Primality
open import Relation.Nullary.Decidable
  using (
    isNo
  )
open import Relation.Binary.PropositionalEquality
\end{code}

\chapter{le vrici}
ni'o la'au le vrici li'u vasru zo'e poi na racli fa lo nu zbasu lo me'oi .chapter.\ poi ke'a xi re vasru ke'a xi pa po'o

\section{la'oi .\F{hWV𝔽}.}
ni'o la'o zoi.\ \F{hWV𝔽} \B x .zoi.\ mu'oi glibau.\ HAMMING weight .glibau.\ la'oi .\B x.

\begin{code}
hWV𝔽 : {a b : ℕ} → Vec (Fin b) a → ℕ
hWV𝔽 = sumᵥ ∘ mapᵥ f
  where
  f : ∀ {a} → Fin a → ℕ
  f (suc _) = 1
  f zero = 0
\end{code}

\section{la'oi .\F{\_div2\_}.}
ni'o gonai ge la'oi .\B b.\ du li no gi ko'a goi la'o zoi.\ \B a \Sym{div2} b .zoi.\ du li no gi ko'a dilcu la'oi .\B a.\ la'oi .\B b.

\begin{code}
_div2_ : ℕ → ℕ → ℕ
_ div2 0 = 0
a div2 (suc b) = a div (suc b)
\end{code}

\section{la'oi .\F{f2f}.}
ni'o ganai ge la'oi .\B a.\ ctaipe la'o zoi.\ \F{Fin} \B n .zoi.\ gi djica lo nu pruce fi lo ctaipe be la'o zoi.\ \F{Fin} \B m .zoi.\ gi gonai ge lo selsni be la'oi .\B a.\ cu dubjavmau la'oi .\B m.\ gi ko'a goi la'o zoi.\ \F{f2f} \B a .zoi.\ sinxa la'oi .\B m.\ gi ko'a sinxa lo selsni be la'oi .\B a.

\begin{code}
postulate f2f : {m n : ℕ} → Fin m → Fin n
\end{code}

\section{la'oi .\F{f𝔽}.}
ni'o ganai la'oi .\B a.\ ctaipe la'o zoi.\ \F{Fin} \B q .zoi.\ gi la'o zoi.\ \F{f𝔽} \B f \B a \B b .zoi.\ sinxa lo nacmecrai be la'o zoi.\ \F{fromℕ} \Sym\$ f (\F{toℕ} \B a) \Sym\$ \F{toℕ} \B b .zoi. ce la'oi .\B q.

\begin{code}
f𝔽 : {n : ℕ} → (ℕ → ℕ → ℕ) → Fin n → Fin n → Fin n
f𝔽 f a b = f2f $ fromℕ $ f (toℕ a) $ toℕ b
\end{code}

\section{la'oi .\F{resize}.}
ni'o cadga fa lo nu lo mu'oi glibau.\ type signature .glibau.\ cu xamgu velcki

\begin{code}
resize : ∀ {a} → {m n : ℕ} → {A : Set a}
       → A → Vec A m → Vec A n
resize {_} {m} {n} {A} x xs = mapTo xs $ replicate x
  where
  postulate
    mapTo : {m' : ℕ} → Vec A m' → Vec A n → Vec A n
\end{code}

\chapter{le fancu poi ke'a srana lo porsi be lo'i me'oi .bit.}

\section{la'oi .\F{nbits}.}
ni'o ko'a goi la'o zoi. \F{nbits} \B q .zoi.\ vasru lo su'o me'oi .bit.\ poi ke'a pagbu la'oi .\B q.  .i ge le pamoi be ko'a cu traji le ka ce'u me'oi .significant.\ kei le ka ce'u mleca gi le romoi be ko'a cu traji le ka ce'u me'oi .significant.

.i la'oi .\F{nbits}.\ cu simsa la'o zoi. \F{Data.Bin.toBits} .zoi.  .i ku'i la'oi .\F{nbits}.\ me'oi .truncate.

\begin{code}
nbits : ∀ {a} → ℕ → Vec (Fin 2) a
nbits = resize zero ∘ fromList ∘ Data.List.map n2f ∘ toNatDigits 2
  where
  n2f = λ f → if f ≡ᵇ 0 then zero else suc zero
\end{code}

\section{la'oi .\F{b2f}.}
ni'o la'o zoi.\ \F{b2f} \B x .zoi.\ sinxa lo namcu poi ke'a selsni la'oi .\B x.\ noi .endi le me'oi .little.

\begin{code}
b2f : {n : ℕ} → Vec (Fin 2) n → Fin $ 2 ^ n
b2f {n} = cond ∘ flip zipᵥ indy ∘ mapᵥ f2f
  where
  postulate
    zf : Fin $ 2 ^ n
  cond : Vec (Fin (2 ^ n) × Fin (2 ^ n)) n → Fin $ 2 ^ n
  cond = foldrᵥ _ (f𝔽 _+_) zf ∘ mapᵥ (uncurry $ f𝔽 _^_)
  indy : Vec (Fin $ 2 ^ n) n
  indy = reverseᵥ $ mapᵥ f2f $ allFin n
\end{code}

\section{la'oi .\F{\_∧𝔹ℕ𝔽\_}.}
ni'o la'o zoi.\ \B a \Sym{∧𝔹ℕ𝔽} \B b .zoi.\ mu'oi glibau.\ bitwise and .glibau.\ la'oi .\B a.\ la'oi .\B b.

\begin{code}
_∧𝔹ℕ𝔽_ : ∀ {a} → ℕ → Fin a → Fin a
_∧𝔹ℕ𝔽_ {a!} a b = toFin $ ∧𝔹ℕ𝔽' (nbits a) $ nbits $ toℕ b
  where
  and𝔽 : Fin 2 → Fin 2 → Fin 2
  and𝔽 (suc zero) (suc zero) = suc zero
  and𝔽 _ _ = zero
  ∧𝔹ℕ𝔽' : ∀ {n} → Vec (Fin 2) n → Vec (Fin 2) n → Vec (Fin 2) n
  ∧𝔹ℕ𝔽' = zipWithᵥ and𝔽
  -- | ni'o narcu'i fa lo nu zmadu la'o zoi. a! .zoi.
  toFin : Vec (Fin 2) a! → Fin a!
  toFin = f2f ∘ b2f
\end{code}

\chapter{la'oi .\D 𝕄.\ je zo'e}
ni'o la'au la'oi .\D M.\ je zo'e li'u vasru le velcki be ko'a goi la'oi .\D M.\ je le pinka be ko'a be'o je ko'a goi le fancu poi ke'a srana la'oi .\D M.\ po'o ku'o je le pinka be ko'a

\section{la'oi .\D 𝕄.}
ni'o ro da poi ke'a mu'oi zoi.\ .\D 𝕄 \B a \B b .zoi.\ zo'u da nacmeimei la'oi .\B a.\ la'oi .\B b.

\subsection{le me'oi .field.\ pe'a ru'e}
ni'o ro da poi ke'a me'oi .\D 𝕄.\ zo'u lo pa moi me'oi .field.\ pe'a ru'e be da cu me'oi .type.\ lo selvau be lo selsni be da

ni'o ro da poi ke'a me'oi .\D 𝕄.\ zo'u lo re moi me'oi .field.\ pe'a ru'e be da cu ni lo selsni be da cu ganra

ni'o ro da poi ke'a me'oi .\D 𝕄.\ zo'u lo ci moi me'oi .field.\ pe'a ru'e be da cu ni lo selsni be da cu rajycla

\begin{code}
𝕄 : ∀ {a} → Set a → ℕ → ℕ → Set a
𝕄 = Vec ∘₂ Vec
\end{code}

\section{la'oi .\Sym{𝕄!!}.}
ni'o cadga fa lo nu le mu'oi glibau.\ type signature .glibau.\ cu xamgu velcki

\begin{code}
_𝕄!!_ : ∀ {a n o} → {A : Set a} → 𝕄 A n o → Fin n → Vec A o
_𝕄!!_ m n = mapᵥ (flip lookup n) m
\end{code}

\section{la'oi .\F{hw𝕄}.}
ni'o la'o zoi.\ \F{hw𝕄} \B t .zoi.\ cu sumji be lo'i mu'oi glibau.\ HAMMING weight .glibau.\ be lo'i ro rajypau pe'a ja co'e be la'oi .\B t.

\begin{code}
hw𝕄 : ∀ {a m n} → 𝕄 (Fin a) m n → ℕ
hw𝕄 = sumᵥ ∘ mapᵥ hWV𝔽
\end{code}

\section{la'oi .\F{rf}.}
ni'o go la'o zoi.\ \F{rf} \D t \D n .zoi.\ zasti gi da mapti le mu'oi glibau.\ reduced row-echelon form .glibau.

\begin{code}
data rf {m n} (q : 𝕄 (Fin 2) m n) : ℕ → Set
  where
  radfrq : rf q $ hw𝕄 q
\end{code}

\chapter{la'oi .\D{MCParam}.\ je zo'e}
ni'o la'au la'oi .\D{MCParam}.\ je zo'e li'u vasru le velcki be ko'a goi la'oi .\D{MCParam}.\ je le pinka be ko'a be'o je ko'a goi le fancu poi ke'a srana la'oi .\D{MCParam}.\ po'o ku'o je le pinka be ko'a

\section{la'oi .\D{MCParam}.}
ni'o ro da poi ke'a me'oi .\D{MCParam}.\ zo'u da sinxa lo me'oi .parameter.\ be lo mu'oi glibau.\ Classic MCELIECE .glibau.\ co'e

\subsection{le me'oi .field.}

\subsubsection{le vrici je me'oi .field.}
\paragraph{la'oi .\F{MCParam.n}.}
ni'o la'o zoi.\ \F{MCParam.n} \D q .zoi.\ ni lo me'oi .code.\ pe la'o zoi.\ \D q .zoi.\ cu clani

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

\subsubsection{le me'oi .field.\ poi ke'a srana le mu'oi glibau.\ symmetric cryptography .glibau.}
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

\paragraph{la'oi .\F{n≤q}.\ je la'oi .\F{t≥2}.\ je la'oi .\F{ν≥μ}.\ je la'oi .\F{ν≤μ+k}.\ je la'oi .\F{σ₁≥m}.\ je la'oi .\F{σ₂≥2*m}.\ je la'oi .\F{m*t<n}.}
ni'o la .varik.\ cu jinvi le du'u le se ctaipe cu banzuka

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
    G : Fin $ 2 ^ ℓ → Fin $ 2 ^ (n + σ₂ * q + σ₁ * t + ℓ)
  k : ℕ
  k = n ∸ m * t
  n-k : ℕ
  n-k = n ∸ k
  field
    n≤q : n ℕ.≤ q
    t≥2 : t ℕ.≥ 2
    ν≥μ : ν ℕ.≥ μ
    ν≤μ+k : ν ℕ.≤ (μ ℕ.+ k)
    σ₁≥m : σ₁ ℕ.≥ m
    σ₂≥2*m : σ₂ ℕ.≥ 2 * m
    m*t<n : m * t ℕ.< n
\end{code}


\section{la'oi .\F{Public}.}
ni'o la'o zoi.\ \F{Public} \B q .zoi.\ me'oi .type.\ lo gubni termifckiku pe la'oi .\B q.

\begin{code}
Public : MCParam → Set
Public p = 𝕄 (Fin 2) (MCParam.k p) $ MCParam.n-k p
\end{code}

\chapter{la'oi .\D{Private}.\ je zo'e}
ni'o la'au la'oi .\D{Private}.\ je zo'e li'u vasru le velcki be ko'a goi la'oi .\D{Private}.\ je le pinka be ko'a be'o je ko'a goi le fancu poi ke'a srana la'oi .\D{Private}.\ po'o ku'o je le pinka be ko'a

\section{la'oi .\D{Private}.}
ni'o ro da poi ke'a me'oi .\D{Private}.\ zo'u da sinxa lo sivni termifckiku pe la'o glibau.\ Classic MCELIECE .glibau.

\subsection{le me'oi .field.}

\paragraph{la'oi .\F{Private.lg}.}
ni'o la'o zoi.\ \F{Private.lg} \B p .zoi.\ nilzilcmi ja zo'e la'o zoi.\ \F{Private.g} \B p .zoi.

\paragraph{la'oi .\F{Private.Γ}.}
ni'o la'o zoi.\ \F{Private.Γ} \B p .zoi.\ lo'i ro cpolinomi'a be fi la'o zoi.\ \F{Private.lg} \B p bei fo ko'a goi la'o zoi.\ \F{Fin} \Sym\$ \F{Private.q} \B .zoi.\ be'o ku pi'u lo'i ro porsi be fi ko'a be'o poi la'o zoi.\ \F{Private.n} \B p .zoi.\ nilzilcmi ke'a

\paragraph{la'oi .\F{Private.s}.}
ni'o la'o zoi.\ \F{Private.s} \Sym\$ \D{Private} \B p .zoi.\ liste lo'i samsle je cu se nilzilcmi la'o zoi.\ \F{toℕ} \Sym\$ \F{MCParam.n} \B p .zoi.

\paragraph{la'oi .\F{Private.g}.}
ni'o la'o zoi.\ \F{Private.g} \B q .zoi.\ cpolinomi'a je cu pa moi lo'i ro selvau be la'o zoi.\ \F{Private.Γ} \B q .zoi.

\paragraph{la'oi .\F{Private.q}.\ je la'oi .\F{Private.n}.}
ni'o la .varik. cu na jinvi le du'u sarcu ja xamgu fa lo nu jmina lo clani velcki be la'oi .\F{Private.q}.\ je la'oi .\F{Private.n}.

.i cumki fa lo nu lo me'oi .private.\ co'e cu vasru la'oi .MCq.\ je la'oi .MCn.  .i ku'i lo nu lo me'oi .private.\ co'e cu na vasru la'oi .MCq.\ je la'oi .MCn.\ cu filri'a lo nu ciksi

\begin{code}
record Private (p : MCParam) : Set
  where
  q = MCParam.q p
  n = MCParam.n p
  field
    lg : ℕ
    Γ : Vec (Fin q) lg × Vec (Fin q) n
    s : Vec (Fin 2) n
  g = proj₁ Γ
\end{code}

\section{la'oi .\F{MatGen}.}
ni'o gonai ko'a goi la'o zoi.\ \F{MatGen} \B x .zoi.\ me'oi .\F{just}.\ lo gubni termifckiku poi ke'a mapti la'oi .\B x.\ gi ko'a me'oi .\F{nothing}.

\begin{code}
MatGen : {p : MCParam} → Private p → Maybe $ Public p
MatGen {p} _ = Data.Maybe.map toPus $ cyst $ repl H~
  where
  tee = MCParam.t p
  enn = MCParam.n p
  mf = 𝕄 (Fin $ MCParam.q p) tee enn
  mftwom = 𝕄 (Fin 2) (tee * MCParam.m p) enn
  postulate
    -- | ni'o ro da zo'u go la'oi .SemiSysForm. ctaipe da
    -- gi da srana le mu'oi glibau. semi-systematic form
    -- .glibau.
    SemiSysForm : Set
    repl : mf → mftwom
    cyst : mftwom → Maybe SemiSysForm
    toPus : SemiSysForm → Public p
    H~ : mf
\end{code}

\chapter{la'oi .\D{KP}. je zo'e}

\section{la'oi .\D{KP}.}
ni'o ro da poi ke'a me'oi .\D{KP}.\ zo'u da sinxa lo mu'oi glibau.\ key pair .glibau.\ pe la'o glibau.\ Classic MCELIECE .glibau.

\subsection{le me'oi .field.}
\paragraph{la'oi .F{KP.pu}.}
ni'o ge ko'a goi la'o zoi.\ \F{KP.pu} \B t .zoi.\ gubni termifckiku gi cadga fa lo nu ko'a mapti la'o zoi.\ \F{KP.pr} \B t .zoi.

\paragraph{la'oi .\F{KP.pr}.}
ni'o ge ko'a goi la'o zoi.\ \F{KP.pr} \B t .zoi.\ sivni termifckiku gi cadga fa lo nu ko'a mapti la'o zoi.\ \F{KP.pr} \B t .zoi.

\begin{code}
record KP (p : MCParam) : Set
  where
  field
    pu : Public p
    pr : Private p
\end{code}

\chapter{le fancu poi lo nu xamgu pilno ke'a cu filri'a lo nu zbasu lo termifckiku}
ni'o la'au le fancu poi ke'a goi ko'a zo'u lo nu xamgu pilno ko'a cu filri'a lo nu zbasu lo termifckiku li'u vasru le velcki be vu'oi le fancu je zo'e vu'o poi ke'a goi ko'a zo'u tu'a ko'a cu filri'a lo nu zbasu lo nu zbasu lo termifckiku

\section{la'oi .\F{FieldOrdering}.}
ni'o la'oi .\F{FieldOrdering}.\ me'oi .implementation.\ ko'a goi la'oi .\textsc{FieldOrdering}.\ poi ke'a se velcki la'o cmene.\ mceliece-20201010.pdf .cmene.\ poi ke'a se me'oi .SHA512.\ zoi zoi.\ \hashish\ .zoi.

\begin{code}
postulate
  FieldOrdering : {p : MCParam}
                → Fin $ MCParam.σ₂ p * MCParam.q p
                → Maybe $ Vec (Fin $ MCParam.q p) $ MCParam.q p
\end{code}

\section{la'oi .\F{SeededKeyGen}.}
ni'o ge ko'a goi la'o zoi.\ \F{KP.pr} \Sym\$ \F{SeededKeyGen} \B q \B l .zoi.\ selkra la'oi .\B l.\ je cu mu'oi glibau.\ Classic MCELIECE .glibau.\ sivni bo termifckiku gi la'o zoi.\ \F{KP.pu} \Sym\$ \F{SeededKeyGen} \B q \B l .zoi.\ cu mapti ko'a

.i ga naja la .varik.\ cu djuno lo du'u lojysra lo du'u me'oi .terminate.\ gi lakne fa lo nu la .varik.\ cu basygau zo'oi .TERMINATING. zoi glibau.\ NON\_TERMINATING .glibau.

\subsection{le velcki}
\begin{code}
{-# NON_TERMINATING #-}
SeededKeyGen : (p : MCParam) → Fin $ 2 ^ (MCParam.ℓ p) → KP p
SeededKeyGen p = (λ (_ , _ , kp) → kp) ∘ SeededKeyGen'
  where
  Vqt = Vec (Fin $ MCParam.q p) $ MCParam.t p
  SeededKeyGen' : Fin $ 2 ^ (MCParam.ℓ p) → Public p × Vqt × KP p
  SeededKeyGen' δ = foo , g , record {pu = foo; pr = pry}
    where
    E = MCParam.G p δ
    rev = Data.Vec.reverse
    b2f' : {m n : ℕ} → Vec (Fin 2) m → Fin n
    b2f' = f2f ∘ b2f
    δ' : Fin $ 2 ^ MCParam.ℓ p
    δ' = b2f $ rev $ takel $ rev themDigits
      where
      takel = Data.Vec.take $ MCParam.ℓ p
      postulate
        blah : ℕ
        themDigits : Vec (Fin 2) $ MCParam.ℓ p + blah
    s : Fin $ MCParam.n p
    s = b2f' themDigits
      where
      postulate
        themDigits : Vec (Fin 2) $ MCParam.n p + 0
    -- | .i cumki fa lo nu cumki fa lo nu la'oi .g.
    -- na me'oi .terminate.
    g : Vqt
    g = maybe id retry tird
      where
      retry = proj₁ $ proj₂ $ SeededKeyGen' δ'
      postulate
        tird : Maybe Vqt
    postulate
      pry : Private p
    foo : Public p
    foo = maybe id (proj₁ $ SeededKeyGen' δ') $ MatGen {p} pry
\end{code}

\section{la'oi .\F{KeyGen}.}
ni'o ge ko'a goi la'o zoi.\ \F{KP.pr} \Sym{<\$>} \F{KeyGen} \B q .zoi.\ me'oi .return.\ ko'a goi lo mu'oi glibau.\ Classic MCELIECE .glibau.\ sivni bo termifckiku poi ke'a mapti la'oi .\B q.\ gi la'o zoi.\ \F{KP.pu} \Sym{<\$>} \F{KeyGen} \B q \B l .zoi.\ me'oi .return.\ lo mu'oi glibau.\ Classic MCELIECE.\ .glibau.\ gubni bo termifckiku poi ke'a mapti ko'a

\subsection{le velcki}

\begin{code}
KeyGen : (p : MCParam) → IO $ KP p
KeyGen p = SeededKeyGen p IO.<$> cunso
  where
  postulate
    cunso : _
\end{code}

\chapter{le fancu poi ke'a goi ko'a zo'u tu'a ko'a cu filri'a lo nu me'oi .encode.\ kei je lo nu me'oi .decode.}

\section{la'oi .\F{Hx}.}
ni'o la'o zoi.\ \F{Hx} \{\B p\} \B T .zoi.\ konkatena lo me'oi .identity.\ nacmeimei la'o zoi.\ \B T .zoi.

\begin{code}
Hx : {p : MCParam}
   → Public p
   → 𝕄 (Fin 2) (MCParam.n-k p + MCParam.k p) $ MCParam.n-k p
Hx {p} T = I ∣ T
  where
  _∣_ : ∀ {a} → {A : Set a} → {m n p : ℕ}
      → 𝕄 A m n → 𝕄 A p n → 𝕄 A (m + p) n
  _∣_ a b = Data.Vec.map (lookup++ a b) $ allFin _
    where
    lookup++ = λ a b n → lookup a n ++ lookup b n
  I : {n : ℕ} → 𝕄 (Fin 2) n n
  I = mapᵥ f $ allFin _
    where
    f : {n : ℕ} → Fin n → Vec (Fin 2) n
    f = λ x → updateAt x (const $ suc zero) $ replicate zero
\end{code}

\section{la'oi .\F{Encode}.}
ni'o la'oi .\F{Encode}.\ me'oi .implementation.\ ko'a goi la'oi .\textsc{Encode}.\ poi ke'a se velcki la'o cmene.\ mceliece-20201010.pdf .cmene.\ poi ke'a se me'oi .SHA512.\ zoi zoi.\ \hashish\ .zoi.

\begin{code}
Encode : {p : MCParam}
       → (e : Vec (Fin 2) $ MCParam.n p)
       → Public p
       → {hWV𝔽 e ≡ MCParam.t p}
       → Vec (Fin 2) $ MCParam.n-k p
Encode {p} e T = moult H e
  where
  H = Hx {p} T
  postulate
    moult : {m n o : ℕ} → 𝕄 (Fin 2) m n → Vec (Fin 2) o
          → Vec (Fin 2) n
\end{code}

\section{la'oi .\F{Decode}.}
ni'o la'oi .\F{Decode}.\ me'oi .implementation.\ ko'a goi la'oi .\textsc{Decode}.\ poi ke'a se velcki la'o cmene.\ mceliece-20201010.pdf .cmene.\ poi ke'a se me'oi .SHA512.\ zoi zoi.\ \hashish\ .zoi.  .i la'oi .\F{Decode}.\ cu na prane pe'a le ka ce'u xe fanva ko'a

\begin{code}
Decode : {p : MCParam}
       → Vec (Fin 2) $ MCParam.n-k p
       → Public p
       → (Σ ℕ $ Vec $ Fin (MCParam.q p))
       → Vec (Fin $ MCParam.q p) $ MCParam.n p
       → Maybe $ Vec (Fin 2) $ MCParam.n p
Decode {p} C₀ bar (_ , g) α' = e Data.Maybe.>>= mapₘ proj₁ ∘ mapti?
  where
  xv = λ f → Vec (Fin 2) $ f p
  dist : xv MCParam.n → xv MCParam.n → ℕ
  dist = Vec≤.length ∘₂ Data.Vec.filter drata ∘₂ zipᵥ
    where
    drata = Data.Bool._≟_ true ∘ isNo ∘ uncurry Data.Fin._≟_
  v : xv MCParam.n
  v = zenbyco'e tv C₀ $ replicate {n = MCParam.n p} zero
    where
    postulate zenbyco'e : _ → _ → Vec (Fin 2) _ → xv MCParam.n
    tv : (λ x → These x x → x) $ Fin 2
    tv = Data.These.fold id id const
  postulate
    sumji : Op₂ $ xv MCParam.n
    c' : Maybe $ Σ (xv MCParam.n) $ λ c → dist c v ℕ.≤ MCParam.t p
  c = Data.Maybe.map proj₁ c'
  e = flip Data.Maybe.map c $ sumji v
  -- | .i lisri
  huck : {m n : ℕ} → Vec (Fin m) n → ℕ
  huck {m} = Data.List.sum ∘ pilji ∘ zipf
    where
    zipf = Data.List.zip (Data.List.upTo n) ∘ toList
    pilji = Data.List.map $ λ (a , b) → a * m ^ toℕ b
  mapti : xv MCParam.n → Set
  mapti e = (hWV𝔽 e ≡ MCParam.t p) × dunli C₀ H*e
    where
    postulate
      dunli : _ → _ → Set
    -- | .i zo'oi .x. cmavlaka'i zo xamgu
    H*e = moult H e
      where
      H = Hx {p} bar
      postulate
        moult : {m n o : ℕ} → 𝕄 (Fin 2) m n → Vec (Fin 2) o
              → Vec (Fin 2) n
  postulate
    mapti? : xv MCParam.n → Maybe $ Σ (xv MCParam.n) mapti
\end{code}
\end{document}
