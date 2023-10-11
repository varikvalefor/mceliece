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
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb{N}}}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{∶}{\ensuremath{\mathnormal\colon\!\!}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb{F}}}}
\newunicodechar{𝕄}{\ensuremath{\mathnormal{\mathbb{M}}}}
\newunicodechar{𝔹}{\ensuremath{\mathnormal{\mathbb{B}}}}
\newunicodechar{ν}{\ensuremath{\mathnormal{\nu}}}
\newunicodechar{μ}{\ensuremath{\mathnormal{\mu}}}
\newunicodechar{τ}{\ensuremath{\mathnormal{\tau}}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\mathrm{b}}}}
\newunicodechar{ˡ}{\ensuremath{\mathnormal{^l}}}
\newunicodechar{ʳ}{\ensuremath{\mathnormal{^r}}}
\newunicodechar{≥}{\ensuremath{\mathnormal{\geq}}}
\newunicodechar{ϕ}{\ensuremath{\mathnormal{\phi}}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\wedge}}}
\newunicodechar{∣}{\ensuremath{\mathnormal{|}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\mathnormal{\forall}}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal{\ell}}}
\newunicodechar{σ}{\ensuremath{\mathnormal{\sigma}}}
\newunicodechar{π}{\ensuremath{\mathnormal{\pi}}}
\newunicodechar{α}{\ensuremath{\mathnormal{\alpha}}}
\newunicodechar{₀}{\ensuremath{\mathnormal{_0}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_\mathsf{l}}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_\mathsf{v}}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_\mathsf{m}}}}
\newunicodechar{≤}{\ensuremath{\mathnormal{\leq}}}
\newunicodechar{⍉}{\ensuremath{\mathnormal{∘\hspace{-0.455em}\backslash}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{δ}{\ensuremath{\mathnormal{\delta}}}
\newunicodechar{⇒}{\ensuremath{\mathnormal{\Rightarrow}}}
\newunicodechar{≰}{\ensuremath{\mathnormal{\nleq}}}
\newunicodechar{∎}{\ensuremath{\mathnormal{\blacksquare}}}
\newunicodechar{⟨}{\ensuremath{\mathnormal{\langle}}}
\newunicodechar{⟩}{\ensuremath{\mathnormal{\rangle}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}

\newcommand\hashish{cbf1 42fe 1ebd b0b2 87a4 4018 340b 8159 7ef1 3a63 6f5d 76f4 6f48 a080 b2bc d3f1 3922 f0f1 5219 94cc 5e71 fb1f b2d9 d9f8 dd3b ffe6 be32 0056 5cca 21c4 28eb 9de1}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\newcommand\sds{\spacefactor\sfcode`.\ \space}

\newcommand\algoritma[1]{\textsc{#1}}

\newcommand\specimp[1]{ni'o la'oi .\F{#1}.\ velcki ja co'e ko'a goi la'oi .\algoritma{#1}.\ poi ke'a se velcki le selvau be la'o cmene.\ mceliece-20201010.pdf .cmene.\ poi ke'a xi re se me'oi .SHA512.\ zoi zoi.\ \hashish\ .zoi.}

% | ni'o cafne fa lo nu su'o da poi ke'a ckupau zo'u lo broda cei me'oi .abstract. be da cu vasru lo cmene be da  .i ko'a goi tu'a la'oi .chapsname. je la'oi .chap. cu rinka lo nu na sarcu fa lo nu broda batkyci'a lo cmene be lo ckupau
%
% .i ko'a na mutce le ka ce'u melbi la .varik.  .i ji'a ko'a na mutce le ka ce'u fegli la .varik.
% .i la .varik. cu curmi lo nu lo tcidu cu stidi
\newcommand\chapsname{}
\newcommand\chap[1]{
	\renewcommand\chapsname{#1}
	\chapter{#1}
}

\newcommand\termineidyr[1]{ga naja la .varik.\ cu djuno lo du'u ma kau ctaipe lo su'u narcu'i fa lo nu la'o zoi.\ #1\ .zoi.\ na me'oi .terminate.\ gi lakne fa lo nu la .varik.\ cu co'e ja cu basygau zo'oi .TERMINATING.\ zoi glibau.\ NON\_TERMINATING .glibau.}

\title{le me'oi .Agda.\ velcki be la'o glibau.\ Classic MCELIECE .glibau.}
\author{la .varik.\ .VALefor.}

\begin{document}

\maketitle

\tableofcontents

\chap{le me'oi .disclaimer.}
ni'o le velcki cu zabna najenai cu mulno

\chap{le terzu'e}
ni'o ko'a goi la'au le me'oi .Agda.\ velcki be la'o glibau.\ Classic MCELIECE .glibau.\ li'u me'oi .Agda.\ co'e\sds  .i tu'a ko'a filri'a lo nu jimpe fi la'o glibau.\ Classic MCELIECE .glibau.

.i la .varik.\ cu mutce le ka ce'u troci lo nu ko'a drani je cu zabna fi la .varik.\ldots kei je nai lo nu ko'a mutce le ka ce'u xi re skami sutra co'e\sds  .i ku'i la .varik.\ cu na tolnei lo nu da'i ko'a drani ba'e je cu skami sutra co'e

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
  using (
    opposite;
    fromℕ<;
    fromℕ;
    zero;
    toℕ;
    Fin;
    suc
  )
  renaming (
    _+_ to _+F_
  )
open import Data.Vec
  using (
    replicate;
    fromList;
    allFin;
    filter;
    lookup;
    toList;
    drop;
    take;
    _∷_;
    Vec;
    []
  )
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
  using (
    if_then_else_;
    false;
    true
  )
open import Data.List
  using (
    _∷_;
    List;
    map;
    reverse;
    []
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
    this;
    that;
    these
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
    curry;
    _×_;
    _,_;
    Σ;
    ∃
  )
open import Data.Nat as ℕ
  using (
    _^_;
    _*_;
    _+_;
    _∸_;
    suc;
    ℕ
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
open import Data.Vec.Bounded
  using (
    Vec≤
  )
open import Truthbrary.Data.Fin
  using (
    mink
  )
open import Truthbrary.Record.Eq
  using (
    _≡ᵇ_;
    _≟_;
    Eq
  )
open import Truthbrary.Record.LLC
  using (
    nu,iork;
    length;
    _++_;
    LL
  )
open import Relation.Nullary.Decidable
  using (
    isYes
  )
open import Truthbrary.Data.Vec.Matrix
  using (
    _∣_;
    I;
    𝕄
  )
open import Relation.Binary.PropositionalEquality

import Data.Nat.Properties as DNP
import Data.Vec.Properties as DVP
\end{code}

\chap{le vrici}
ni'o la'au \chapsname\ li'u vasru zo'e poi na racli fa lo nu zbasu lo ckupau poi ke'a xi re vasru ke'a xi pa po'o

\section{la'oi .\F{hWV𝔽}.}
ni'o ko'a goi la'o zoi.\ \F{hWV𝔽} \B x .zoi.\ mu'oi glibau.\ HAMMING weight .glibau.\ la'oi .\B x.\sds  .i sa'u nai ko'a nilzilcmi lo'i ro co'e ja cmima be la'o zoi.\ \B x .zoi.\ be'o poi ke'a na du la'oi .\AgdaInductiveConstructor{zero}.

\begin{code}
hWV𝔽 : {a b : ℕ} → Vec (Fin b) a → ℕ
hWV𝔽 = sumᵥ ∘ mapᵥ f
  where
  f : ∀ {a} → Fin a → ℕ
  f (suc _) = 1
  f zero = 0
\end{code}

\section{la'oi .\F{\AgdaUnderscore{}div2\AgdaUnderscore}.}
ni'o ga jonai ga je la'oi .\B b.\ du li no gi ko'a goi la'o zoi.\ \B a \F{div2} b .zoi.\ du li no gi ko'a dilcu la'oi .\B a.\ la'oi .\B b.

\begin{code}
_div2_ : Op₂ ℕ
_ div2 0 = 0
a div2 (suc b) = a div (suc b)
\end{code}

\section{la'oi .\F{f2f}.}
ni'o ga naja la'oi .\B a.\ ctaipe la'o zoi.\ \D{Fin} \B n .zoi.\ gi ga jonai ga je lo selsni be la'oi .\B a.\ cu dubjavmau la'oi .\B m.\ gi ko'a goi la'o zoi.\ \F{f2f} \Sym\{\B n\Sym\} \Sym\{\B m\Sym\} \B a .zoi.\ sinxa la'oi .\B m.\ gi ko'a sinxa lo selsni be la'oi .\B a.

\begin{code}
f2f : {m n : ℕ} → Fin m → Fin n
f2f = {!!}
\end{code}

\section{la'oi .\F{f𝔽}.}
ni'o ga naja la'oi .\B a.\ ctaipe la'o zoi.\ \D{Fin} \B q .zoi.\ gi la'o zoi.\ \F{f𝔽} \B f \B a \B b .zoi.\ sinxa lo nacmecrai be la'o zoi.\ \F{fromℕ} \OpF \$ \B f \Sym(\F{toℕ} \B a\Sym) \OpF \$ \F{toℕ} \B b .zoi.\ ce la'o zoi.\ \F{\AgdaUnderscore∸\AgdaUnderscore} \B q \AgdaNumber 1 .zoi.

\begin{code}
f𝔽 : {n : ℕ} → Op₂ ℕ → Op₂ $ Fin n
f𝔽 f a b = f2f $ fromℕ $ f (toℕ a) $ toℕ b
\end{code}

\section{la'oi .\F{coerce}.}
ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu ciksi la'oi .\F{coerce}.\ bau la .lojban.

\begin{code}
coerce : ∀ {a} → {A B : Set a} → A ≡ B → A → B
coerce refl = id
\end{code}

\section{la'oi .\F{resize}.}
ni'o ga jonai ga je ctaipe la'o zoi.\ \B n\ \OpF{ℕ.≤}\ \B m\ .zoi.\ gi ko'a goi la'o zoi.\ \F{resize}\ \Sym\{\AgdaUnderscore\Sym\}\ \Sym\{\B m\Sym\}\ \Sym\{\B n\Sym\}\ \B t\ .zoi.\ du la'o zoi.\ \F{drop}\ \OpF \$\ \B m\ \OpF ∸\ \B n\ .zoi.\ gi ko'a du la'o zoi.\ \F{\AgdaUnderscore++\AgdaUnderscore}\ \OpF \$\ \F{replicate}\ \B t\ .zoi.

\begin{code}
resize : ∀ {a} → {m n : ℕ} → {A : Set a}
       → A → Vec A m → Vec A n
resize {_} {m} {n} {A} x xs = xt $ n ℕ.≤? m
  where
  xt : Dec $ n ℕ.≤ m → Vec A n
  xt (yes z) = drop (m ∸ n) $ coc xs
    where
    coc = coerce $ sym $ cong (Vec A) $ DNP.m∸n+n≡m z
  xt (no z) = flip coerce padin $ cong (Vec A) bitc
    where
    padin : Vec A $ n ∸ m + m
    padin = replicate x ++ xs
    bitc : n ∸ m + m ≡ n
    bitc = DNP.m∸n+n≡m $ DNP.≰⇒≥ z

  open ≡-Reasoning

  -- ni'o la .varik. cu djica ko'a goi lo nu
  -- zoi zoi. resize x xs .zoi. ja zo'e je zo'e cu basti
  -- zoi zoi. xt (yes g) .zoi. je zo'e
  -- .i tu'a la'o zoi. resize x xs .zoi. ja zo'e cu
  -- zmadu tu'a la'o zoi. xt (yes g) .zoi. je zo'e le
  -- ka la .varik. cu jinvi le du'u ce'u sampu kei kei je
  -- le ka la .varik. cu se frili fa lo nu jimpe fi ce'u
  --
  -- .i la .varik. cu jinvi le du'u ko'a se sarcu lo
  -- nu ciksi lo ctaipe be le su'u ga naja ctaipe
  -- lo su'u la'o zoi. m .zoi. dubjavme'a
  -- la'o zoi. n .zoi. gi la'o zoi. resize x xs .zoi.
  -- du la'o zoi. xt (yes g) .zoi. ja zo'e

  flipko : ∀ {a} → {A B : Set a}
         → (x : A)
         → (d : A ≡ B)
         → x ≡ coerce (sym d) (coerce d x)
  flipko _ refl = refl

  dropis : (g : n ℕ.≤ m)
         → let v≡v = sym $ cong (Vec A) $ DNP.m∸n+n≡m g in
           let xs' = coerce v≡v xs in
           (_≡_
             xs
             (coerce
               (cong (Vec A) $ DNP.m∸n+n≡m g)
               (take (m ∸ n) xs' ++ xt (yes g))))
  dropis g = sym $ begin
    coerce k konk ≡⟨ cong (coerce k) $ DVP.take-drop-id (m ∸ n) xs' ⟩
    coerce k xs' ≡⟨ cong (flip coerce xs') $ symref k ⟩
    coerce (sym $ sym k) xs' ≡⟨ sym $ flipko xs $ sym k ⟩
    xs ∎
    where
    k = cong (Vec A) $ DNP.m∸n+n≡m g
    xs' = coerce (sym k) xs
    konk : Vec A $ m ∸ n + n
    konk = take (m ∸ n) xs' ++ xt (yes g)
    symref : ∀ {a} → {A B : Set a}
           → (t : A ≡ B)
           → t ≡ sym (sym t)
    symref refl = refl

  takis : (g : ¬ (n ℕ.≤ m))
        → let k = DNP.m∸n+n≡m $ DNP.≰⇒≥ g in
          let sink = sym $ cong (Vec A) k in
          xs ≡ drop (n ∸ m) (coerce sink $ xt $ no g)
  takis g = sym $ begin
    drop (n ∸ m) konk ≡⟨ cong (drop $ n ∸ m) konkydus ⟩
    drop (n ∸ m) (pad ++ xs) ≡⟨ sym $ dropdus pad xs ⟩
    xs ∎
    where
    pad = replicate x
    k = DNP.m∸n+n≡m $ DNP.≰⇒≥ g
    konk : Vec A $ n ∸ m + m
    konk = flip coerce (xt $ no g) $ sym $ cong (Vec A) k
    konkydus : konk ≡ pad ++ xs
    konkydus = sym $ flipko (pad ++ xs) $ cong (Vec A) k
    dropdus : ∀ {a} → {A : Set a} → {m n : ℕ}
            → (x : Vec A m)
            → (z : Vec A n)
            → z ≡ drop (length x) (x ++ z)
    dropdus [] _ = refl
    dropdus (x ∷ xs) = subst (_≡_ _) (d xs x) ∘ dropdus xs
      where
      d : ∀ {a} → {A : Set a} → {m n : ℕ}
        → (x : Vec A m)
        → {z : Vec A n}
        → (e : A)
        → (_≡_
            (drop (length x) $ x ++ z)
            (drop (length $ e ∷ x) $ e ∷ x ++ z))
      d x {z} e = sym $ DVP.unfold-drop (length x) e $ x ++ z
\end{code}

\section{la .\F{dist}.}
ni'o la'o zoi.\ \F{dist} \Sym ⦃ \B Q \Sym ⦄ \B x \B z \B d\ .zoi.\ nilzilcmi lo'i ro ctaipe be la'o zoi.\ \D{Fin} OpF \$ \F{LL.l} \B Q \AgdaUnderscore \B x\ .zoi. be'o poi lo meirmoi be ke'a bei la'o zoi.\ \B x\ .zoi.\ cu drata lo meirmoi be ke'a bei la'o zoi.\ \B z\ .zoi.

\begin{code}
dist : ∀ {a} → {A : Set a}
     → ⦃ Q : LL A ⦄ → ⦃ Eq $ LL.e Q ⦄
     → (x z : A)
     → LL.l Q x ≡ LL.l Q z
     → ℕ
dist ⦃ Q ⦄ x z d = Vec≤.length $ filter drata $ zipᵥ x' z'
  where
  drata = _≟_ false ∘ isYes ∘ uncurry _≟_
  x' = flip coerce (LL.vec Q x) $ cong (Vec $ LL.e Q) d
  z' = LL.vec Q z
\end{code}

\section{la .\F{pausyk}.}
ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu la .varik.\ cu ciski la .\F{pausyk}.\ bau la .lojban.

\begin{code}
pausyk : (b e : ℕ) → ∃ $ λ n → suc n ≡ ℕ.suc b ^ e
pausyk _ 0 = 0 , refl
pausyk b' (ℕ.suc e) = _ , sym mips
  where
  mips = begin
    b ^ ℕ.suc e ≡⟨ refl ⟩
    b * (b ^ e) ≡⟨ sym $ cong (_*_ b) $ proj₂ $ pausyk b' e ⟩
    b * suc z₁ ≡⟨ refl ⟩
    b * (1 + z₁) ≡⟨ cong (_*_ b) $ DNP.+-comm 1 z₁ ⟩
    b * (z₁ + 1) ≡⟨ DNP.*-distribˡ-+ b z₁ 1 ⟩
    b * z₁ + b * 1 ≡⟨ cong bizpu $ DNP.*-identityʳ b ⟩
    b * z₁ + b ≡⟨ refl ⟩
    b * z₁ + (1 + b') ≡⟨ cong bizpu $ DNP.+-comm 1 b' ⟩
    b * z₁ + (b' + 1) ≡⟨ sym $ DNP.+-assoc (b * z₁) b' 1 ⟩
    b * z₁ + b' + 1 ≡⟨ flip DNP.+-comm 1 $ b * z₁ + b' ⟩
    suc (b * z₁ + b') ∎
    where
    z₁ = proj₁ $ pausyk b' e
    b = ℕ.suc b'
    bizpu = _+_ $ b * z₁
    open Relation.Binary.PropositionalEquality.≡-Reasoning
\end{code}

\chap{le fancu poi ke'a srana lo porsi be lo'i me'oi .bit.}

\section{la'oi .\F{nbits}.}
ni'o ko'a goi la'o zoi.\ \F{nbits} \B q .zoi.\ vasru lo su'o me'oi .bit.\ poi ke'a pagbu la'oi .\B q.\sds  .i ga je le pamoi be ko'a cu traji le ka ce'u me'oi .significant.\ kei le ka ce'u zenba gi le romoi be ko'a cu traji le ka ce'u me'oi .significant.

.i la'oi .\F{nbits}.\ simsa la'o zoi.\ \F{Data.Bin.toBits} .zoi.\ je ku'i cu me'oi .truncate.

\begin{code}
nbits : {n : ℕ} → ℕ → Vec (Fin 2) n
nbits = resize zero ∘ fromList ∘ reverse ∘ proj₁ ∘ toDigits 2
\end{code}

\section{la'oi .\F{b2f}.}
ni'o la'o zoi.\ \F{b2f} \B x .zoi.\ sinxa lo namcu poi ke'a selsni la'oi .\B x.\ noi .endi le me'oi .big.

\begin{code}
b2f : {m n : ℕ} → Vec (Fin $ suc m) n → Fin $ suc m ^ n
b2f {m'} {n} = cond ∘ flip zipᵥ indy ∘ mapᵥ f2f
  where
  m = suc m'
  indy : flip Vec n $ Fin $ m ^ n
  indy = reverseᵥ $ mapᵥ f2f $ allFin n
  zf = mink zero $ proj₂ $ pausyk m' n
  cond : let X = Fin $ m ^ n in flip Vec n $ X × X → X
  cond = foldrᵥ _ (f𝔽 _+_) zf ∘ mapᵥ pilji
    where
    pilji = uncurry $ f𝔽 $ λ a b → a * m ^ b
\end{code}

\subsection{le se zvati}
ni'o xu cadga fa lo nu muvgau le velcki be ko'a goi la .\F{b2f}.\ lo drata be la'au \chapsname\ li'u\sds  .i ko'a mapti lo na ctaipe be ko'e goi la'o zoi.\ \D{Fin} \AgdaNumber 2\ .zoi.\ je ku'i cu co'e ja selbi'o le mapti be lo ctaipe be ko'e be'o po'o\sds  .i la .varik.\ cu na birti lo du'u ma kau ckupau je cu zmadu la'au \chapsname\ li'u le ka ko'a mapti ce'u

\section{la'oi .\F{\AgdaUnderscore∧𝔹ℕ𝔽\AgdaUnderscore}.}
ni'o la'o zoi.\ \B a \OpF{∧𝔹ℕ𝔽} \B b .zoi.\ mu'oi glibau.\ bitwise and .glibau.\ la'oi .\B a.\ la'oi .\B b.

\begin{code}
_∧𝔹ℕ𝔽_ : {n : ℕ} → ℕ → Op₁ $ Fin n
_∧𝔹ℕ𝔽_ a = toFin ∘ zipWithᵥ (f𝔽 _*_) (nbits a) ∘ nbits ∘ toℕ
  where
  -- | ni'o narcu'i fa lo nu zmadu la'o zoi. a! .zoi.
  toFin : {n : ℕ} → Vec (Fin 2) n → Fin n
  toFin = f2f ∘ b2f
\end{code}

\section{la'oi .\F{hw𝕄}.}
ni'o la'o zoi.\ \F{hw𝕄} \B t .zoi.\ grisumji lo se cmima poi ro da zo'u ga jo da cmima ke'a gi su'o de poi ke'a xi re co'e ja rajypau la'o zoi.\ \B t\ .zoi.\ zo'u da mu'oi glibau.\ HAMMING weight .glibau.\ de

\begin{code}
hw𝕄 : {a m n : ℕ} → 𝕄 (Fin a) m n → ℕ
hw𝕄 = sumᵥ ∘ mapᵥ hWV𝔽
\end{code}

\section{la'oi .\F{moult}.}
ni'o la'o zoi.\ \F{moult}\ \B a\ \B b\ .zoi.\ pilji la'o zoi.\ \B a\ .zoi.\ la'o zoi.\ \B b\ .zoi.

\begin{code}
moult : {m n o : ℕ} → 𝕄 (Fin 2) m n → Vec (Fin 2) o
      → Vec (Fin 2) n
moult = {!!}
\end{code}

\chap{la'oi .\AgdaRecord{MCParam}.\ je zo'e}
ni'o la'au \chapsname\ li'u vasru le velcki be ko'a goi la'oi .\AgdaRecord{MCParam}.\ be'o je le pinka be ko'a be'o je ko'a goi le fancu poi ke'a srana la'oi .\AgdaRecord{MCParam}.\ po'o ku'o je le pinka be ko'a

\section{la'oi .\AgdaRecord{MCParam}.}
ni'o lo ro ctaipe be la'oi .\AgdaRecord{MCParam}.\ cu me'oi .parameter.\ lo mu'oi glibau.\ Classic MCELIECE .glibau.\ co'e

\subsection{le me'oi .\AgdaKeyword{field}.}

\subsubsection{le vrici je me'oi .\AgdaKeyword{field}.}
\paragraph{la'oi .\F{MCParam.n}.}
ni'o la'o zoi.\ \F{MCParam.n} \B q .zoi.\ ni clani fa lo me'oi .code.\ pe la'o zoi.\ \B q .zoi.

\paragraph{la'oi .\F{MCParam.m}.}
ni'o la'o zoi.\ \F{MCParam.m} \B q .zoi.\ reldugri lo ni barda fa lo selvau be lo me'oi .\AgdaKeyword{field}.

\paragraph{la'oi .\F{MCParam.t}.}
ni'o la'o zoi.\ \F{MCParam.t} \B q .zoi.\ ni cumki fa lo nu rinka ja gasnu ja co'e lo nu binxo lo drani

\paragraph{la'oi .\F{MCParam.f}.}
ni'o la'o zoi.\ \F{MCParam.f} \B q .zoi.\ me'oi .monic.\ je me'oi .irreducible.\ cpolynomi'a fi la'o zoi.\ \F{MCParam.m} \B q .zoi\ldots je cu co'e

\paragraph{la'oi .\F{MCParam.F}.}
ni'o la'o zoi.\ \F{MCParam.F} \B q .zoi.\ me'oi .monic.\ je me'oi .irreducible.\ cpolynomi'a fi la'o zoi.\ \F{MCParam.t} \B q .zoi\ldots je cu co'e

\paragraph{la'oi .\F{MCParam.k}.}
ni'o la'o zoi.\ \F{MCParam.k} \B q .zoi.\ me'oi .dimension.\ lo me'oi .code.\ pe la'oi .\B q.

\paragraph{la'oi .\F{MCParam.ν}.}
ni'o la'o zoi.\ \F{MCParam.ν} \B q .zoi.\ dubjavmau li no je cu dubjavme'a lo sumji be la'o zoi.\ \F{MCParam.k} \B q .zoi.\ bei la'o zoi.\ \F{MCParam.μ \B q} .zoi.

\paragraph{la'oi .\F{MCParam.ν}.}
ni'o la'o zoi.\ \F{MCParam.μ} \B q .zoi.\ dubjavmau li no je cu dubjavme'a la'o zoi.\ \F{MCParam.ν \B q} .zoi.\ je lo vujnu be la'o zoi.\ \F{MCParam.ν} \B q .zoi.\ bei la'o zoi.\ \F{MCParam.k} \B q .zoi.

\subsubsection{le me'oi .\AgdaKeyword{field}.\ poi ke'a srana le mu'oi glibau.\ symmetric cryptography .glibau.}
\paragraph{la'oi .\F{MCParam.ℓ}.}
ni'o la'o zoi.\ \F{MCParam.ℓ} \B q .zoi.\ ni clani fa lo me'oi .output.\ be la'o zoi.\ \F{MCParam.H} \B q .zoi.\

\paragraph{la'oi .\F{MCParam.H}.}
ni'o la'o zoi.\ \F{MCParam.H} \B q \B n .zoi.\ me'oi .hash.\ la'o zoi.\ \B n\ .zoi.

\paragraph{la'oi .\F{MCParam.σ₁}.}
ni'o la'o zoi.\ \F{MCParam.σ₁} \B q .zoi.\ me'oi .arbitrary.

\paragraph{la'oi .\F{MCParam.σ₂}.}
.i la'o zoi.\ \F{MCParam.σ₂} \B q .zoi.\ ji'a me'oi .arbitrary.

\paragraph{la'oi .\F{MCParam.G}.}
ni'o la'o zoi.\ \F{MCParam.G} \B q \B x .zoi.\ me'oi .pseudorandom.

\paragraph{lo ctaipe be lo su'u dubjavme'a ja co'e}
ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu ciksi la'oi .\F{n≤q}.\ ja la'oi .\F{t≥2}.\ ja la'oi .\F{ν≥μ}.\ ja la'oi .\F{ν≤μ+k}.\ ja la'oi .\F{σ₁≥m}.\ ja la'oi .\F{σ₂≥2*m}.\ ja la \F{ctejau}\ bau la .lojban.

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
    ν≤μ+k : ν ℕ.≤ μ + k
    σ₁≥m : σ₁ ℕ.≥ m
    σ₂≥2*m : σ₂ ℕ.≥ 2 * m
    ctejau : m * t ℕ.< n
\end{code}

\chap{la'oi .\F{Public}.}
ni'o la'au \chapsname\ li'u vasru le velcki be ko'a goi la'oi .\F{Public}.\ be'o je le pinka be ko'a be'o je ko'a goi le fancu poi ke'a srana la'oi .\F{Public}.\ po'o ku'o je le pinka be ko'a

\section{la'oi .\F{Public}.}
ni'o la'o zoi.\ \F{Public} \B q .zoi.\ se ctaipe lo gubni termifckiku pe la'oi .\B q.

\begin{code}
Public : MCParam → Set
Public p = 𝕄 (Fin 2) (MCParam.k p) $ MCParam.n-k p
\end{code}

\chap{la'oi .\AgdaRecord{Private}.\ je zo'e}
ni'o la'au \chapsname\ li'u vasru le velcki be ko'a goi la'oi .\AgdaRecord{Private}.\ ja zo'e be'o je le pinka be ko'a be'o je ko'e goi le fancu poi ke'a srana vu'oi ko'a ja zo'e vu'o po'o ku'o je le pinka be ko'e

\section{la'oi .\AgdaRecord{Private}.}
ni'o la'oi .\AgdaRecord{Private}.\ se ctaipe lo sivni termifckiku pe la'o glibau.\ Classic MCELIECE .glibau.

\subsection{le me'oi .\AgdaKeyword{field}.}

\paragraph{la'oi .\F{Private.lg}.}
ni'o la'o zoi.\ \F{Private.lg} \B p .zoi.\ nilzilcmi ja co'e la'o zoi.\ \F{Private.g} \B p .zoi.

\paragraph{la'oi .\F{Private.Γ}.}
ni'o la'o zoi.\ \F{Private.Γ} \B p .zoi.\ lo'i ro cpolinomi'a be fi la'o zoi.\ \F{Private.lg} \B p bei fo ko'a goi la'o zoi.\ \D{Fin} \F \$ \F{Private.q} \B .zoi.\ be'o ku pi'u lo'i ro porsi be fi ko'a be'o poi la'o zoi.\ \F{Private.n} \B p .zoi.\ nilzilcmi ke'a

\paragraph{la'oi .\F{Private.s}.}
ni'o la'o zoi.\ \F{Private.s} \B p .zoi.\ porsi fi lo'i samsle je cu se nilzilcmi la'o zoi.\ \F{MCParam.n} \B p .zoi.

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
ni'o la'o zoi.\ \F{MatGen} \B x .zoi.\ me'oi .\F{nothing}.\ jonai cu me'oi .\F{just}.\ lo gubni termifckiku poi ke'a mapti la'oi .\B x.

ni'o pilno le mu'oi glibau.\ semi-systematic form .glibau.\ ki'u le su'u ga je la .varik.\ cu djica lo nu mapti lo ro broda cei co'e gi le mu'oi glibau.\ systematic form .glibau.\ cu na mapti lo su'o broda

\begin{code}
MatGen : {p : MCParam}
       → (pr : Private p)
       → (Maybe
           (_×_
             (Public p)
             (_×_
               (Vec ℕ $ MCParam.μ p)
               (_×_
                 (typeOf $ Private.Γ pr)
                 (∃ $ Vec $ Fin $ MCParam.q p)))))
MatGen {p} _ = {!!}
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

\chap{la'oi .\AgdaRecord{KP}.\ je zo'e}

\section{la'oi .\AgdaRecord{KP}.}
ni'o la'oi .\AgdaRecord{KP}.\ se ctaipe lo mu'oi glibau.\ Classic MCELIECE .glibau.\ mu'oi glibau.\ key pair .glibau.

.i ga naja la'o zoi.\ \B t .zoi.\ ctaipe la'o zoi.\ \AgdaRecord{KP}\ \AgdaUnderscore\ .zoi.\ gi cadga fa lo nu la'o zoi.\ \F{proj₂} \B t .zoi.\ sivni termifckiku je cu mapti la'o zoi.\ \B t\ .zoi.\ je la'o zoi.\ \F{proj₁} \B t .zoi.

\begin{code}
KP : MCParam → Set
KP p = Public p × Private p
\end{code}

\chap{le fancu poi tu'a ke'a filri'a lo nu zbasu lo termifckiku}
ni'o la'au \chapsname\ li'u vasru le velcki be vu'oi le fancu je zo'e vu'o poi tu'a ke'a filri'a lo nu zbasu lo termifckiku

\section{la'oi .\F{Irreducible}.}
ni'o \specimp{Irreducible}

\begin{code}
Irreducible : {p : MCParam}
            → Fin $ 2 ^ (MCParam.σ₁ p * MCParam.t p)
            → Maybe $ Vec (Fin $ MCParam.q p) $ MCParam.t p
Irreducible {p} d = if proj₁ g ≡ᵇ t then just (proj₂ g) else nothing
  where
  t = MCParam.t p
  g : ∃ $ Vec $ Fin $ MCParam.q p
  g = {!!} , {!!}
\end{code}

\section{la'oi .\F{FieldOrdering}.}
ni'o \specimp{FieldOrdering}

\begin{code}
FieldOrdering : {p : MCParam}
              → Fin $ MCParam.σ₂ p * MCParam.q p
              → Maybe $ Vec (Fin $ MCParam.q p) $ MCParam.q p
FieldOrdering {p} f = mapₘ α $ sartre $ indice a
  where
  indice : ∀ {a} → {n : ℕ} → {A : Set a}
         → Vec A n → Vec (A × Fin n) n
  indice = flip zipᵥ $ allFin _
  q = MCParam.q p
  v = flip Vec q $ Fin $ MCParam.σ₂ p
  vex = flip Vec q $ Fin (MCParam.σ₂ p) × Fin q
  a : v
  a = {!!}
  α : vex → Vec (Fin q) q
  α = mapᵥ $ λ (a , π) → toF $ sumᵥ $ mapᵥ (prod a π) $ allFin m
    where
    m = MCParam.m p
    toF : ℕ → Fin _
    toF = {!!}
    prod = λ a π j → toℕ π * {!!} ^ (m ∸ 1 ∸ toℕ j)
  sartre : vex → Maybe vex
  sartre = mapₘ jort ∘ panci
    where
    -- | ni'o pilno la .jort. lo nu me'oi .lexicographic.
    -- porganzu
    jort : ∀ {a} → {A : Set a} → {m n : ℕ}
         → Op₁ $ flip Vec n $ Fin m × A
    jort = {!!}
    panci : vex → Maybe vex
    panci v = mapₘ (λ _ → v) $ decToMaybe $ Dec (nu,iork v) ∋ {!!}
\end{code}

\section{la'oi .\F{FixedWeight}.}
ni'o \specimp{FixedWeight}

ni'o \termineidyr{\F{FixedWeight}}

\begin{code}
{-# NON_TERMINATING #-}
FixedWeight : {p : MCParam}
            → (IO $ Σ
                (Vec (Fin 2) $ MCParam.n p)
                (λ e → hWV𝔽 e ≡ MCParam.t p))
FixedWeight {p} = {!!} IO.>>= restart? ∘ FixedWeight'
  where
  OT = Σ (Vec (Fin 2) $ MCParam.n p) $ λ e
         → hWV𝔽 e ≡ MCParam.t p
  -- | ni'o cumki fa lo nu cumki fa lo nu tu'a
  -- la'oi .restart?. rinka lo nu na me'oi .terminate.
  restart? : Maybe OT → IO OT
  restart? = maybe pure $ FixedWeight {p}
  -- | ni'o la'o zoi. mceliece.pdf .zoi. vasru le velcki
  -- be la'oi .τ. be'o poi ke'a na zabna  .i la .varik. cu
  -- na birti
  τ : ℕ
  τ = if MCParam.n p ≡ᵇ MCParam.q p then MCParam.t p else {!!}
  FixedWeight' : Fin $ 2 ^ (MCParam.σ₁ p * τ) → Maybe OT
  FixedWeight' b = mapₘ (proj₁,₂ ∘ e') a
    where
    proj₁,₂ : ∀ {a b c}
            → {A : Set a} → {B : A → Set b} → {C : A → Set c}
            → ∃ (λ a' → B a' × C a')
            → ∃ B
    proj₁,₂ (a , b , _) = a , b
    d : Vec ℕ τ
    d = mapᵥ (λ j → sumᵥ $ mapᵥ (uijis j) $ allFin m) $ allFin τ
      where
      m = MCParam.m p
      uijis : Fin τ → Fin m → ℕ
      uijis j i = 2 ^ toℕ i * toℕ (lookup b' {!!})
        where
        b' = nbits {MCParam.σ₁ p * τ} $ toℕ b
    a : Maybe $ Vec (Fin $ MCParam.n p) $ MCParam.t p
    a = toVec? (Data.List.take (MCParam.t p) mlen) >>=ₘ panci?
      where
      -- | ni'o zo .mlen. cmavlaka'i
      -- lu mleca la .n. li'u
      mlen : List $ Fin $ MCParam.n p
      mlen = Data.List.mapMaybe id $ map mlen? $ toList d
        where
        mlen? : (n : ℕ) → Maybe $ Fin $ MCParam.n p
        mlen? n = mapₘ fromℕ< $ decToMaybe $ n ℕ.<? MCParam.n p
      V = Vec (Fin $ MCParam.n p) $ MCParam.t p
      panci? : V → Maybe V
      panci? = {!!}
      toVec? : List $ Fin $ MCParam.n p → Maybe V
      toVec? l with length l ≟ MCParam.t p
      ... | no _ = nothing
      ... | yes d = just $ flip coerce (fromList l) $ cong (Vec _) d
    e' : (a : _)
       → Σ (Vec (Fin 2) (MCParam.n p)) $ λ e
         → hWV𝔽 e ≡ MCParam.t p
         × let el = Data.List.allFin _ in
           (_≡_
             el
             (flip Data.List.filter
               el
               (λ i → suc zero ≟ lookup e (lookup a i))))
    e' = {!!}
\end{code}

\section{la'oi .\F{Encap}.}
ni'o \specimp{Encap}

\begin{code}
Encap : {p : MCParam}
      → let F = Fin $ 2 ^ MCParam.ℓ p in
        IO $ Vec (Fin 2) (MCParam.n-k p) × F × F
Encap {p} = Encap' {p} IO.<$> FixedWeight {p}
  where
  Encap' : {p : MCParam}
         → (Σ (Vec (Fin 2) $ MCParam.n p) $ λ e
              → hWV𝔽 e ≡ MCParam.t p)
         → let F = Fin $ 2 ^ MCParam.ℓ p in
           Vec (Fin 2) (MCParam.n-k p) × F × F
  Encap' = {!!}
\end{code}

\section{la'oi .\F{SeededKeyGen}.}
ni'o \specimp{SeededKeyGen}

.i la'o zoi.\ \F{SeededKeyGen} \B p \B δ\ .zoi.\ .orsi li re lo mu'oi glibau.\ Classic MCELIECE .glibau.\ ke sivni termifckiku lo mapti be ko'a

ni'o \termineidyr{\F{SeededKeyGen}}

\begin{code}
{-# NON_TERMINATING #-}
SeededKeyGen : (p : MCParam) → Fin $ 2 ^ MCParam.ℓ p → KP p
SeededKeyGen p = SeededKeyGen'
  where
  -- | .i cumki fa lo nu cumki fa lo nu tu'a lo nu
  -- me'oi .recurse. cu rinka lo nu na me'oi .terminate.
  SeededKeyGen' : Fin $ 2 ^ MCParam.ℓ p → KP p
  SeededKeyGen' δ = fromMaybe (SeededKeyGen' δ') mapti?
    where
    E = MCParam.G p δ
    δ' : Fin $ 2 ^ MCParam.ℓ p
    δ' = b2f $ reverseᵥ $ nbits {MCParam.ℓ p} $ toℕ $ rev E
      where
      rev : {n : ℕ} → Op₁ $ Fin n
      rev = opposite

      module Veritas where
        zivle : {n : ℕ} → (t : Fin n) → t ≡ rev (rev t)
        zivle = {!!}
    mapti? : Maybe $ KP p
    mapti? = (apₘ ∘₂ mapₘ) _,_ (sivni >>=ₘ MatGen') sivni
      where
      MatGen' = mapₘ proj₁ ∘ MatGen
      sivni = g? >>=ₘ λ (j , lg , g) → just record {
        lg = lg;
        Γ = g , j;
        s = nbits $ toℕ $ b2f $ nbits {MCParam.n p} $ toℕ E
        }
        where
        g? : let Vq = Vec $ Fin $ MCParam.q p in
             Maybe $ Vq (MCParam.n p) × ∃ Vq
        g? = mapₘ (λ g → {!!} , _ , g) $ Irreducible {p} {!!}
\end{code}

\section{la'oi .\F{KeyGen}.}
ni'o la'o zoi.\ \F{KeyGen} \B p\ .zoi.\ me'oi .\F{pure}.\ lo me'oi .pseudorandom.\ poi ke'a .orsi li re lo mu'oi glibau.\ Classic MCELIECE .glibau.\ ke sivni termifckiku lo mapti be ko'a

\begin{code}
KeyGen : (p : MCParam) → IO $ KP p
KeyGen p = SeededKeyGen p IO.<$> cunso
  where
  cunso = b2f {n = MCParam.ℓ p} IO.<$> {!!}
\end{code}

\chap{le fancu poi tu'a ke'a filri'a lo nu me'oi .encode.\ kei je lo nu me'oi .decode.}
ni'o ko'a goi la'au \chapsname\ li'u vasru le velcki be ko'e goi vu'oi le fancu poi tu'a ke'a filri'a lo nu me'oi .encode.\ ku'o je le fancu poi tu'a ke'a filri'a lo nu me'oi .decode.\ ge'u je le pinka be ko'e\sds  .i la .varik.\ cu na birti le du'u sarcu fa tu'a le me'oi .abstract.\ be ko'a

\section{la'oi .\F{Hx}.}
ni'o la'o zoi.\ \F{Hx} \B p \B T .zoi.\ konkatena lo me'oi .identity.\ nacmeimei la'o zoi.\ \B T .zoi.

\begin{code}
Hx : (p : MCParam)
   → Public p
   → 𝕄 (Fin 2) (MCParam.n p) $ MCParam.n-k p
Hx p = coerce (cong matmid n∸k+k≡n) ∘ _∣_ (I zero $ suc zero)
  where
  matmid = λ i → 𝕄 (Fin 2) i $ MCParam.n-k p
  n∸k+k≡n = DNP.m∸n+n≡m $ DNP.m∸n≤m (MCParam.n p) m*t
    where
    m*t = MCParam.m p * MCParam.t p
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

\section{la'oi .\F{Decode}.}
ni'o \specimp{Decode}\sds  .i la'oi .\F{Decode}.\ na prane pe'a le ka ce'u xe fanva ko'a

\begin{code}
Decode : {p : MCParam}
       → Vec (Fin 2) $ MCParam.n-k p
       → Public p
       → ∃ $ Vec $ Fin $ MCParam.q p
       → Vec (Fin $ MCParam.q p) $ MCParam.n p
       → Maybe $ Vec (Fin 2) $ MCParam.n p
Decode {p} C₀ bar (_ , g) α' = e >>=ₘ mapₘ proj₁ ∘ mapti?
  where
  xv = λ f → Vec (Fin 2) $ f p
  v : xv MCParam.n
  v = zenbyco'e tv C₀ $ replicate zero
    where
    zenbyco'e : _ → xv MCParam.n-k → Op₁ $ xv MCParam.n
    zenbyco'e = {!!}
    tv : (λ t → These t t → t) $ Fin 2
    tv = Data.These.fold id id const
  c' : Maybe $ ∃ $ λ c → dist c v refl ℕ.≤ MCParam.t p
  c' = {!!}
  c = mapₘ proj₁ c'
  e = flip mapₘ c $ zipWithᵥ (f𝔽 _+_) v
  mapti : xv MCParam.n → Set
  mapti e = Σ (hWV𝔽 e ≡ MCParam.t p) $ _≡_ C₀ ∘ Encode p e bar
  mapti? : xv MCParam.n → Maybe $ Σ (xv MCParam.n) mapti
  mapti? e = mapₘ (_,_ e) $ dus >>=ₘ λ x → mapₘ (_,_ x) $ enk x
    where
    dus = decToMaybe $ _ ≟ _
    enk : (x : hWV𝔽 e ≡ MCParam.t p)
        → Maybe $ C₀ ≡ Encode p e bar x
    enk = {!!}
\end{code}
\end{document}
