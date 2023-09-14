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

\newcommand\hashish{cbf1 42fe 1ebd b0b2 87a4 4018 340b 8159 7ef1 3a63 6f5d 76f4 6f48 a080 b2bc d3f1 3922 f0f1 5219 94cc 5e71 fb1f b2d9 d9f8 dd3b ffe6 be32 0056 5cca 21c4 28eb 9de1}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

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

\title{le me'oi .Agda.\ velcki be la'o glibau.\ Classic MCELIECE .glibau.}
\author{la .varik.\ .VALefor.}

\begin{document}

\maketitle

\tableofcontents

\chap{le me'oi .disclaimer.}
ni'o le velcki cu na zabna je cu na mulno

\chap{le terfi'i ja co'e}
ni'o ko'a goi la'au le me'oi .Agda.\ velcki be la'o glibau.\ Classic MCELIECE .glibau.\ li'u me'oi .Agda.\ co'e  .i tu'a ko'a cu filri'a lo nu jimpe fi le mu'oi glibau.\ Classic MCELIECE .glibau.

.i la .varik.\ cu mutce le ka ce'u troci lo nu ko'a drani je cu zabna fi la .varik.\ldots kei je nai lo nu ko'a mutce le ka ce'u xi re sutra  .i ku'i la .varik.\ cu na tolnei lo nu da'i ko'a drani ba'e je cu sutra

\chap{le me'oi .preamble.}
ni'o la'au \chapsname\ li'u vasru le .importe ja me'oi .pragma.\ selsku

\begin{code}
{-# OPTIONS --guardedness #-}

open import IO
open import Data.Fin
  using (
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
  using (
    _≡ᵇ_;
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
open import Algebra.Structures
open import Data.Nat.Primality
open import Truthbrary.Data.Fin
open import Truthbrary.Record.Eq
  using (
    _≟_
  )
open import Relation.Nullary.Decidable
  using (
    isNo
  )
open import Relation.Binary.PropositionalEquality

import Data.Nat.Properties as DNP
import Data.Vec.Properties as DVP
\end{code}

\chap{le vrici}
ni'o la'au \chapsname\ li'u vasru zo'e poi na racli fa lo nu zbasu lo me'oi .chapter.\ poi ke'a xi re vasru ke'a xi pa po'o

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
ni'o ga jonai ga je la'oi .\B b.\ du li no gi ko'a goi la'o zoi.\ \B a \F{div2} b .zoi.\ du li no gi ko'a dilcu la'oi .\B a.\ la'oi .\B b.

\begin{code}
_div2_ : ℕ → ℕ → ℕ
_ div2 0 = 0
a div2 (suc b) = a div (suc b)
\end{code}

\section{la'oi .\F{f2f}.}
ni'o ga naja ga je la'oi .\B a.\ ctaipe la'o zoi.\ \D{Fin} \B n .zoi.\ gi djica lo nu pruce fi lo ctaipe be la'o zoi.\ \D{Fin} \B m .zoi.\ gi ga jonai ga je lo selsni be la'oi .\B a.\ cu dubjavmau la'oi .\B m.\ gi ko'a goi la'o zoi.\ \F{f2f} \B a .zoi.\ sinxa la'oi .\B m.\ gi ko'a sinxa lo selsni be la'oi .\B a.

\begin{code}
f2f : {m n : ℕ} → Fin m → Fin n
f2f = {!!}
\end{code}

\section{la'oi .\F{f𝔽}.}
ni'o ganai la'oi .\B a.\ ctaipe la'o zoi.\ \D{Fin} \B q .zoi.\ gi la'o zoi.\ \F{f𝔽} \B f \B a \B b .zoi.\ sinxa lo nacmecrai be la'o zoi.\ \F{fromℕ} \F \$ f \Sym(\F{toℕ} \B a\Sym) \F \$ \F{toℕ} \B b .zoi.\ ce la'oi .\B q.

\begin{code}
f𝔽 : {n : ℕ} → (ℕ → ℕ → ℕ) → Fin n → Fin n → Fin n
f𝔽 f a b = f2f $ fromℕ $ f (toℕ a) $ toℕ b
\end{code}

\section{la'oi .\F{resize}.}
ni'o ga jonai ga je ctaipe la'o zoi.\ \B n\ \F{ℕ.≤}\ \B m\ .zoi.\ gi ko'a goi la'o zoi.\ \F{resize}\ \Sym\{\_\Sym\}\ \Sym\{\B m\Sym\}\ \Sym\{\B n\Sym\}\ \B t\ .zoi.\ du la'o zoi.\ \F{drop}\ \F \$\ \B m\ \F ∸\ \B n\ .zoi.\ gi ko'a du la'o zoi.\ \F{\_++\_}\ \F \$\ \F{replicate}\ \B t\ .zoi.

\begin{code}
resize : ∀ {a} → {m n : ℕ} → {A : Set a}
       → A → Vec A m → Vec A n
resize {_} {m} {n} {A} x xs = xt $ n ℕ.≤? m
  where
  coerce : ∀ {a} → {A B : Set a} → A ≡ B → A → B
  coerce refl = id
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
    drop (n ∸ m) (pad ++ xs) ≡⟨ dropdus pad xs ⟩
    xs ∎
    where
    pad = replicate x
    k = DNP.m∸n+n≡m $ DNP.≰⇒≥ g
    konk : Vec A $ n ∸ m + m
    konk = coerce (sym $ cong (Vec A) k) $ xt $ no g
    konkydus : konk ≡ pad ++ xs
    konkydus = sym $ flipko (pad ++ xs) $ cong (Vec A) k
    dropdus : ∀ {a} → {A : Set a} → {m n : ℕ}
            → (x : Vec A m)
            → (z : Vec A n)
            → drop (length x) (x ++ z) ≡ z
    dropdus [] _ = refl
    dropdus (x ∷ xs) = subst (flip _≡_ _) (d xs x) ∘ dropdus xs
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

\chap{le fancu poi ke'a srana lo porsi be lo'i me'oi .bit.}

\section{la'oi .\F{nbits}.}
ni'o ko'a goi la'o zoi.\ \F{nbits} \B q .zoi.\ vasru lo su'o me'oi .bit.\ poi ke'a pagbu la'oi .\B q.  .i ge le pamoi be ko'a cu traji le ka ce'u me'oi .significant.\ kei le ka ce'u zenba gi le romoi be ko'a cu traji le ka ce'u me'oi .significant.

.i la'oi .\F{nbits}.\ cu simsa la'o zoi.\ \F{Data.Bin.toBits} .zoi.  .i ku'i la'oi .\F{nbits}.\ me'oi .truncate.

\begin{code}
nbits : {n : ℕ} → ℕ → Vec (Fin 2) n
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
  zf = mink zero $ proj₂ $ zerpaus _ n
    where
    zerpaus : (b e : ℕ) → ∃ $ λ n → suc n ≡ ℕ.suc b ^ e
    zerpaus _ 0 = 0 , refl
    zerpaus b' (ℕ.suc e) = _ , sym mips
      where
      mips = begin
        b ^ ℕ.suc e ≡⟨ refl ⟩
        b * (b ^ e) ≡⟨ sym $ cong (_*_ b) $ proj₂ $ zerpaus b' e ⟩
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
        z₁ = proj₁ $ zerpaus b' e
        b = ℕ.suc b'
        bizpu = _+_ $ b * z₁
        open Relation.Binary.PropositionalEquality.≡-Reasoning
  cond : flip Vec n $ Fin (2 ^ n) × Fin (2 ^ n) → Fin $ 2 ^ n
  cond = foldrᵥ _ (f𝔽 _+_) zf ∘ mapᵥ pilji
    where
    pilji = uncurry $ f𝔽 $ curry $ λ (a , b) → a * 2 ^ b
  indy : flip Vec n $ Fin $ 2 ^ n
  indy = reverseᵥ $ mapᵥ f2f $ allFin n
\end{code}

\section{la'oi .\F{\_∧𝔹ℕ𝔽\_}.}
ni'o la'o zoi.\ \B a \AgdaOperator{\F{∧𝔹ℕ𝔽}} \B b .zoi.\ mu'oi glibau.\ bitwise and .glibau.\ la'oi .\B a.\ la'oi .\B b.

\begin{code}
_∧𝔹ℕ𝔽_ : {n : ℕ} → ℕ → Fin n → Fin n
_∧𝔹ℕ𝔽_ a b = toFin $ zipWithᵥ and𝔽 (nbits a) $ nbits $ toℕ b
  where
  and𝔽 : Op₂ $ Fin 2
  and𝔽 (suc zero) (suc zero) = suc zero
  and𝔽 _ _ = zero
  -- | ni'o narcu'i fa lo nu zmadu la'o zoi. a! .zoi.
  toFin : {n : ℕ} → Vec (Fin 2) n → Fin n
  toFin = f2f ∘ b2f
\end{code}

\chap{la'oi .\F 𝕄.\ je zo'e}
ni'o la'au \chapsname\ li'u vasru le velcki be ko'a goi la'oi .\F 𝕄.\ je le pinka be ko'a be'o je ko'a goi le fancu poi ke'a srana la'oi .\F 𝕄.\ po'o ku'o je le pinka be ko'a

\section{la'oi .\F 𝕄.}
ni'o ro da poi ke'a ctaipe la'o zoi.\ .\F 𝕄 \B A \B a \B b .zoi.\ zo'u da nacmeimei la'oi .\B a.\ la'oi .\B b.\ je cu vasru lo ctaipe be la'oi .\B A.

ni'o la'o zoi.\ \F 𝕄 \F ℕ 3 3 \F ∋ ((1 \F ∷ 2 \F \F ∷ 3 \F ∷ \F{[]}) \F ∷ (4 \F ∷ 5 \F ∷ 6 \F ∷ \F{[]}) \F ∷ (7 \F ∷ 8 \F ∷ 9 \F ∷ \F{[]}) \F ∷ \F{[]}) .zoi.\ du le nacmeimei poi ke'a du la'o cmaci.
\[
	\begin{bmatrix}
		1 & 2 & 3 \\
		4 & 5 & 6 \\
		7 & 8 & 9
	\end{bmatrix}
\]
.cmaci.

\begin{code}
𝕄 : ∀ {a} → Set a → ℕ → ℕ → Set a
𝕄 = Vec ∘₂ Vec
\end{code}

\section{la'oi .\F{𝕄!!}.}
ni'o cadga fa lo nu le mu'oi glibau.\ type signature .glibau.\ cu xamgu velcki

\begin{code}
_𝕄!!_ : ∀ {a n o} → {A : Set a} → 𝕄 A n o → Fin n → Vec A o
_𝕄!!_ m n = mapᵥ (flip lookup n) m
\end{code}

\section{la'oi .\F{hw𝕄}.}
ni'o la'o zoi.\ \F{hw𝕄} \B t .zoi.\ sumji lo'i mu'oi glibau.\ HAMMING weight .glibau.\ be lo'i ro rajypau pe'a ja co'e be la'oi .\B t.

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

\subsection{le me'oi .field.}

\subsubsection{le vrici je me'oi .field.}
\paragraph{la'oi .\F{MCParam.n}.}
ni'o la'o zoi.\ \F{MCParam.n} \B q .zoi.\ ni lo me'oi .code.\ pe la'o zoi.\ \D q .zoi.\ cu clani

\paragraph{la'oi .\F{MCParam.m}.}
ni'o la'o zoi.\ \F{MCParam.m} \B q .zoi.\ reldugri lo ni lo me'oi .field.\ cu barda

\paragraph{la'oi .\F{MCParam.t}.}
ni'o la'o zoi.\ \F{MCParam.t} \B q .zoi.\ ni me'oi .guarantee.\ le du'u cumki fa lo nu rinka ja gasnu ja co'e lo nu binxo lo drani

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
.i la'o zoi.\ \F{MCParam.σ₂} \B q .zoi.\ ji'a me'oi .arbitrary.

\paragraph{la'oi .\F{MCParam.G}.}
ni'o la'o zoi.\ \F{MCParam.G} \B q \B x .zoi.\ me'oi .pseudorandom.

\paragraph{le ctaipe be lo su'u dubjavme'a ja co'e}
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

\section{la'oi .\F{Public}.}
ni'o la'o zoi.\ \F{Public} \B q .zoi.\ se ctaipe lo gubni termifckiku pe la'oi .\B q.

\begin{code}
Public : MCParam → Set
Public p = 𝕄 (Fin 2) (MCParam.k p) $ MCParam.n-k p
\end{code}

\chap{la'oi .\AgdaRecord{Private}.\ je zo'e}
ni'o la'au \chapsname\ li'u vasru le velcki be ko'a goi la'oi .\AgdaRecord{Private}.\ be'o je le pinka be ko'a be'o je ko'a goi le fancu poi ke'a srana la'oi .\AgdaRecord{Private}.\ po'o ku'o je le pinka be ko'a

\section{la'oi .\AgdaRecord{Private}.}
ni'o la'oi .\AgdaRecord{Private}.\ se ctaipe lo sivni termifckiku pe la'o glibau.\ Classic MCELIECE .glibau.

\subsection{le me'oi .field.}

\paragraph{la'oi .\F{Private.lg}.}
ni'o la'o zoi.\ \F{Private.lg} \B p .zoi.\ nilzilcmi ja co'e la'o zoi.\ \F{Private.g} \B p .zoi.

\paragraph{la'oi .\F{Private.Γ}.}
ni'o la'o zoi.\ \F{Private.Γ} \B p .zoi.\ lo'i ro cpolinomi'a be fi la'o zoi.\ \F{Private.lg} \B p bei fo ko'a goi la'o zoi.\ \D{Fin} \F \$ \F{Private.q} \B .zoi.\ be'o ku pi'u lo'i ro porsi be fi ko'a be'o poi la'o zoi.\ \F{Private.n} \B p .zoi.\ nilzilcmi ke'a

\paragraph{la'oi .\F{Private.s}.}
ni'o la'o zoi.\ \F{Private.s} \F \$ \AgdaRecord{Private} \B p .zoi.\ porsi fi lo'i samsle je cu se nilzilcmi la'o zoi.\ \F{MCParam.n} \B p .zoi.

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
  repl = {!!}
  cyst : mftwom → Maybe SemiSysForm
  cyst = {!!}
  toPus : SemiSysForm → Public p
  toPus = {!!}
  H~ : mf
  H~ = {!!}
\end{code}

\chap{la'oi .\AgdaRecord{KP}.\ je zo'e}

\section{la'oi .\AgdaRecord{KP}.}
ni'o la'oi .\AgdaRecord{KP}.\ se ctaipe lo mu'oi glibau. Classic MCELIECE .glibau.\ mu'oi glibau.\ key pair .glibau.

\subsection{le me'oi .field.}
\paragraph{la'oi .\F{KP.pu}.}
ni'o ge ko'a goi la'o zoi.\ \F{KP.pu} \B t .zoi.\ gubni termifckiku gi cadga fa lo nu ko'a mapti la'o zoi.\ \F{KP.pr} \B t .zoi.

\paragraph{la'oi .\F{KP.pr}.}
ni'o ge ko'a goi la'o zoi.\ \F{KP.pr} \B t .zoi.\ sivni termifckiku gi cadga fa lo nu ko'a mapti la'o zoi.\ \F{KP.pu} \B t .zoi.

\begin{code}
record KP (p : MCParam) : Set
  where
  field
    pu : Public p
    pr : Private p
\end{code}

\chap{le fancu poi tu'a ke'a filri'a lo nu zbasu lo termifckiku}
ni'o la'au \chapsname\ li'u vasru le velcki be vu'oi le fancu je zo'e vu'o poi tu'a ke'a filri'a lo nu zbasu lo termifckiku

\section{la'oi .\F{Irreducible}.}
ni'o \specimp{Irreducible}

\begin{code}
Irreducible : {p : MCParam}
            → Fin $ 2 ^ (MCParam.σ₁ p * MCParam.t p)
            → Maybe $ Vec (Fin $ MCParam.q p) $ MCParam.t p
Irreducible = {!!}
\end{code}

\section{la'oi .\F{FieldOrdering}.}
ni'o \specimp{FieldOrdering}

\begin{code}
FieldOrdering : {p : MCParam}
              → Fin $ MCParam.σ₂ p * MCParam.q p
              → Maybe $ Vec (Fin $ MCParam.q p) $ MCParam.q p
FieldOrdering {p} f = mapₘ {!!} $ sartre $ indice a
  where
  indice : ∀ {a} → {n : ℕ} → {A : Set a}
         → Vec A n → Vec (A × Fin n) n
  indice = flip zipᵥ $ Data.Vec.allFin _
  q = MCParam.q p
  v = flip Vec q $ Fin $ MCParam.σ₂ p
  vex = flip Vec q $ Fin (MCParam.σ₂ p) × Fin q
  a : v
  a = {!!}
  sartre : vex → Maybe vex
  sartre = mapₘ jort ∘ panci
    where
    -- | ni'o pilno la .jort. lo nu me'oi .lexicographic.
    -- porganzu
    jort : ∀ {a} → {A : Set a} → {m n : ℕ}
         → Op₁ $ flip Vec n $ Fin m × A
    jort = {!!}
    panci : vex → Maybe vex
    panci = {!!}
\end{code}

\section{la'oi .\F{FixedWeight}.}
ni'o \specimp{FixedWeight}

ni'o ga naja la .varik.\ cu djuno lo du'u ma kau ctaipe lo su'u narcu'i fa lo nu na me'oi .terminate.\ gi lakne fa lo nu la .varik.\ cu basygau zo'oi .TERMINATING.\ zoi glibau.\ NON\_TERMINATING .glibau.

\begin{code}
{-# NON_TERMINATING #-}
FixedWeight : {p : MCParam}
            → (IO $
                Σ (Vec (Fin 2) $ MCParam.n p) $ λ e
                  → hWV𝔽 e ≡ MCParam.t p)
FixedWeight {p} = {!!} IO.>>= restart? ∘ FixedWeight'
  where
  OT = Σ (Vec (Fin 2) $ MCParam.n p) $ λ e
         → hWV𝔽 e ≡ MCParam.t p
  -- | ni'o cumki fa lo nu cumki fa lo nu tu'a
  -- la'oi .restart?. rinka lo nu na me'oi .terminate.
  restart? : Maybe OT → IO OT
  restart? = maybe pure $ FixedWeight {p}
  τ : ℕ
  τ with MCParam.n p ≟ MCParam.q p
  ... | yes _ = MCParam.t p
  ... | no _ = {!!}
  FixedWeight' : Fin $ 2 ^ (MCParam.σ₁ p * τ) → Maybe OT
  FixedWeight' b = mapₘ (proj₁,₂ ∘ e') a
    where
    proj₁,₂ : ∀ {a b c}
            → {A : Set a} → {B : A → Set b} → {C : A → Set c}
            → Σ A (λ a' → B a' × C a')
            → Σ A B
    proj₁,₂ (a , b , _) = a , b
    d : Vec ℕ τ
    d = mapᵥ {!!} $ upToᵥ τ
      where
      upToᵥ : (n : ℕ) → Vec ℕ n
      upToᵥ 0 = []
      upToᵥ s@(suc n) = s ∷ upToᵥ n
    a : Maybe $ Vec (Fin $ MCParam.n p) $ MCParam.t p
    a = {!!}
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
         → let F = Fin $ 2 ^ MCParam.ℓ p in
           (Σ (Vec (Fin 2) $ MCParam.n p) $ λ e
              → hWV𝔽 e ≡ MCParam.t p)
           → Vec (Fin 2) (MCParam.n-k p) × F × F
  Encap' = {!!}
\end{code}

\section{la'oi .\F{SeededKeyGen}.}
ni'o ge ko'a goi la'o zoi.\ \F{KP.pr} \F \$ \F{SeededKeyGen} \B q \B l .zoi.\ mu'oi glibau.\ Classic MCELIECE .glibau.\ ke sivni termifckiku gi la'o zoi.\ \F{KP.pu} \F \$ \F{SeededKeyGen} \B q \B l .zoi.\ cu mapti ko'a

.i ga naja la .varik.\ cu djuno lo du'u ma kau ctaipe lo su'u la'oi .\F{SeededKeyGen}.\ me'oi .terminate.\ gi lakne fa lo nu la .varik.\ cu co'e ja cu basygau zo'oi .TERMINATING.\ zoi glibau.\ NON\_TERMINATING .glibau.

\subsection{le velcki}
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
    b2f' : {m n : ℕ} → Vec (Fin 2) m → Fin n
    b2f' = f2f ∘ b2f
    δ' : Fin $ 2 ^ MCParam.ℓ p
    δ' = b2f $ reverseᵥ $ nbits {MCParam.ℓ p} $ toℕ $ rev E
      where
      rev : {n : ℕ} → Fin n → Fin n
      rev {suc _} = Data.Fin.opposite

      module Veritas where
        zivle : {n : ℕ} → (t : Fin n) → t ≡ rev (rev t)
        zivle = {!!}
    mapti? : Maybe $ KP p
    mapti? = mapₘ₂ gumgau {!!} {!!}
      where
      Vqt = Vec (Fin $ MCParam.q p) $ MCParam.t p
      gumgau : Public p → Vqt → KP p
      gumgau T _ = record {pu = T; pr = {!!}}
      mapₘ₂ : ∀ {a b c} → {A : Set a} → {B : Set b} → {C : Set c}
            → (A → B → C) → Maybe A → Maybe B → Maybe C
      mapₘ₂ = ap ∘₂ mapₘ
      s : Fin $ 2 ^ MCParam.n p
      s = b2f $ nbits {MCParam.n p} $ toℕ E
\end{code}

\section{la'oi .\F{KeyGen}.}
ni'o ge ko'a goi la'o zoi.\ \F{KP.pr} \F{<\$>} \F{KeyGen} \B q .zoi.\ me'oi .return.\ ko'a goi lo mu'oi glibau.\ Classic MCELIECE .glibau.\ sivni bo termifckiku poi ke'a mapti la'oi .\B q.\ gi la'o zoi.\ \F{KP.pu} \F{<\$>} \F{KeyGen} \B q \B l .zoi.\ me'oi .return.\ lo mu'oi glibau.\ Classic MCELIECE.\ .glibau.\ gubni bo termifckiku poi ke'a mapti ko'a

\subsection{le velcki}

\begin{code}
KeyGen : (p : MCParam) → IO $ KP p
KeyGen p = SeededKeyGen p IO.<$> cunso
  where
  cunso = b2f {MCParam.ℓ p} IO.<$> {!!}
\end{code}

\chap{le fancu poi tu'a ke'a filri'a lo nu me'oi .encode.\ kei je lo nu me'oi .decode.}

\section{la'oi .\F{Hx}.}
ni'o la'o zoi.\ \F{Hx} \B p \B T .zoi.\ konkatena lo me'oi .identity.\ nacmeimei la'o zoi.\ \B T .zoi.

\begin{code}
Hx : (p : MCParam)
   → Public p
   → 𝕄 (Fin 2) (MCParam.n-k p + MCParam.k p) $ MCParam.n-k p
Hx p = _∣_ I
  where
  _∣_ : ∀ {a} → {A : Set a} → {m n p : ℕ}
      → 𝕄 A m n → 𝕄 A p n → 𝕄 A (m + p) n
  _∣_ a b = mapᵥ (lookup++ a b) $ allFin _
    where
    lookup++ = λ a b n → lookup a n ++ lookup b n
  I : {n : ℕ} → 𝕄 (Fin 2) n n
  I = mapᵥ f $ allFin _
    where
    f = λ x → updateAt x (const $ suc zero) $ replicate zero
\end{code}

\section{la'oi .\F{Encode}.}
ni'o \specimp{Encode}

\begin{code}
Encode : (p : MCParam)
       → (e : Vec (Fin 2) $ MCParam.n p)
       → Public p
       → {hWV𝔽 e ≡ MCParam.t p}
       → Vec (Fin 2) $ MCParam.n-k p
Encode p e T = moult H e
  where
  H = Hx p T
\end{code}

\section{la'oi .\F{Decode}.}
ni'o \specimp{Decode}\sds  .i la'oi .\F{Decode}.\ cu na prane pe'a le ka ce'u xe fanva ko'a

\begin{code}
Decode : {p : MCParam}
       → Vec (Fin 2) $ MCParam.n-k p
       → Public p
       → ∃ $ Vec $ Fin $ MCParam.q p
       → Vec (Fin $ MCParam.q p) $ MCParam.n p
       → Maybe $ Vec (Fin 2) $ MCParam.n p
Decode {p} C₀ bar (_ , g) α' = e Data.Maybe.>>= mapₘ proj₁ ∘ mapti?
  where
  xv = λ f → Vec (Fin 2) $ f p
  dist : {n : ℕ} → Vec (Fin 2) n → Vec (Fin 2) n → ℕ
  dist = Vec≤.length ∘₂ filter drata ∘₂ zipᵥ
    where
    drata = _≟_ true ∘ isNo ∘ uncurry _≟_
  v : xv MCParam.n
  v = zenbyco'e tv C₀ $ replicate {n = MCParam.n p} zero
    where
    zenbyco'e : _ → _ → Vec (Fin 2) _ → xv MCParam.n
    zenbyco'e = {!!}
    tv : (λ t → These t t → t) $ Fin 2
    tv = Data.These.fold id id const
  sumji : Op₂ $ xv MCParam.n
  sumji = zipWithᵥ $ f𝔽 _+_
  c' : Maybe $ Σ (xv MCParam.n) $ λ c → dist c v ℕ.≤ MCParam.t p
  c' = {!!}
  c = mapₘ proj₁ c'
  e = flip mapₘ c $ sumji v
  -- | .i lisri
  huck : {m n : ℕ} → Vec (Fin m) n → ℕ
  huck {m} {n} = Data.List.sum ∘ pilji ∘ indice ∘ toList
    where
    indice = Data.List.zip $ Data.List.upTo n
    pilji = Data.List.map $ λ (a , b) → a * m ^ toℕ b
  mapti : xv MCParam.n → Set
  mapti e = (hWV𝔽 e ≡ MCParam.t p) × (C₀ ≡ H*e)
    where
    H*e = moult H e
      where
      H = Hx p bar
  mapti? : xv MCParam.n → Maybe $ Σ (xv MCParam.n) mapti
  mapti? e with hWV𝔽 e ℕ.≟ MCParam.t p
  ... | yes x = {!!}
  ... | no _ = nothing
\end{code}
\end{document}
