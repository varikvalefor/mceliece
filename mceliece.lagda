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
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{ˡ}{\ensuremath{\mathnormal{^\AgdaFontStyle{l}}}}
\newunicodechar{ʳ}{\ensuremath{\mathnormal{^\AgdaFontStyle{r}}}}
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
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_\AgdaFontStyle{l}}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_\AgdaFontStyle{v}}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_\AgdaFontStyle{m}}}}
\newunicodechar{ₚ}{\ensuremath{\mathnormal{_\AgdaFontStyle{p}}}}
\newunicodechar{≤}{\ensuremath{\mathnormal{\leq}}}
\newunicodechar{⍉}{\ensuremath{\mathnormal{∘\hspace{-0.455em}\backslash}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{δ}{\ensuremath{\mathnormal{\delta}}}
\newunicodechar{⇒}{\ensuremath{\mathnormal{\Rightarrow}}}
\newunicodechar{≰}{\ensuremath{\mathnormal{\nleq}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\hspace{-0.3em}|}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{|\hspace{-0.3em}\rbrace}}}
\newunicodechar{▹}{\ensuremath{\mathnormal{\triangleright}}}

% | ni'o tu'a le canlu lerfu cu milxe le ka ce'u fegli kei je ku'i cu mutce le ka ce'u filri'a lo nu na me'oi .overfull.
%
% ni'o ki'u le smimlu la .varik. cu nelci le su'u so'i da poi ke'a jufra fi la .lojban. zo'u cmalu je cmavo fa lo so'e valsi pe da
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

.i la .varik.\ cu mutce le ka ce'u troci lo nu ko'a drani je cu zabna fi la .varik.\ldots kei kei je nai cu mutce le ka ce'u troci lo nu ko'a mutce le ka ce'u xi re skami sutra co'e\sds  .i ku'i la .varik.\ na toldji lo nu da'i ko'a drani ba'e je cu skami sutra co'e

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
    zipWith to zipWithᵥ;
    reverse to reverseᵥ;
    foldr to foldrᵥ;
    map to mapᵥ;
    sum to sumᵥ;
    zip to zipᵥ
  )
open import Function
  renaming (
    -- | ni'o smimlu le .asycy'i'is. co'e...
    -- je ku'i cu mleca fi le ka ce'u fegli la .varik.
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
  using (
    reverse;
    List;
    _∷_;
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
    these;
    this;
    that
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
    map₂;
    dmap;
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
open import Truthbrary.Record.SR
  using (
    show
  )
open import Truthbrary.Record.LLC
  using (
    nu,iork;
    length;
    _++_;
    map;
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

import Agda.Builtin.IO as ABIO
import Data.Nat.Properties as DNP
import Data.Vec.Properties as DVP
import Data.List.Relation.Unary.All as Listal
\end{code}

\chap{le vrici}
ni'o la'au \chapsname\ li'u vasru zo'e poi na racli fa lo nu zbasu lo ckupau poi srana ke'a xi pa fa lo ro selvau be ke'a xi re

\section{la'oi .\F{hWV𝔽}.}
ni'o ko'a goi la'o zoi.\ \F{hWV𝔽} \B x\ .zoi.\ mu'oi glibau.\ HAMMING weight .glibau.\ la'oi .\B x.\sds  .i sa'u nai ko'a nilzilcmi lo'i ro co'e poi la'oi .\AgdaInductiveConstructor{zero}.\ na meirmoi ke'a fo la'oi .\B x.

\begin{code}
hWV𝔽 : {a b : ℕ} → Vec (Fin b) a → ℕ
hWV𝔽 = sumᵥ ∘ mapᵥ f
  where
  f : ∀ {a} → Fin a → ℕ
  f (suc _) = 1
  f zero = 0
\end{code}

\section{la'oi .\F{\AgdaUnderscore{}div2\AgdaUnderscore}.}
ni'o ga jonai li no du la'oi .\B b.\ je ko'a goi la'o zoi.\ \B a \OpF{div2} \B b\ .zoi.\ gi ko'a dilcu la'oi .\B a.\ la'oi .\B b.

\begin{code}
_div2_ : Op₂ ℕ
_ div2 0 = 0
a div2 (suc b) = a div (suc b)
\end{code}

\section{la'oi .\F{f2f}.}
ni'o ga naja la'oi .\B a.\ ctaipe la'o zoi.\ \D{Fin} \B m\ .zoi.\ gi ga jonai ko'e goi la'o zoi.\ \F{toℕ}\ \B a\ .zoi.\ du ko'a goi la'o zoi.\ \F{toℕ} \OpF \$ \F{f2f} \Sym\{\B n\Sym\} \Sym\{\B n\Sym\} \B a\ .zoi.\ gi ga je ko'e dubjavmau la'oi .\B m.\ gi ko'a du la'oi .\B n.

\begin{code}
f2f : {m n : ℕ} → Fin m → Fin $ suc n
f2f f with toℕ f ℕ.<? _
... | yes t = Data.Fin.fromℕ< t
... | no _ = Data.Fin.fromℕ< $ DNP.n<1+n _
\end{code}

\section{la'oi .\F{f𝔽}.}
ni'o ga naja la'oi .\B a.\ ctaipe la'o zoi.\ \D{Fin} \B q\ .zoi.\ gi la'o zoi.\ \F{toℕ} \OpF \$ \F{f𝔽} \B f \B a \B b\ .zoi.\ nacmecrai la'o zoi.\ \F{fromℕ} \OpF \$ \B f \Sym(\F{toℕ} \B a\Sym) \OpF \$ \F{toℕ} \B b\ .zoi.\ ce la'o zoi.\ \F{\AgdaUnderscore{}∸\AgdaUnderscore} \B q \AgdaNumber 1\ .zoi.

\begin{code}
f𝔽 : {n : ℕ} → Op₂ ℕ → Op₂ $ Fin $ suc n
f𝔽 f = f2f ∘₂ fromℕ ∘₂ f on toℕ
\end{code}

\section{la'oi .\F{coerce}.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi la'oi .\F{coerce}.\ bau la .lojban.

\begin{code}
coerce : ∀ {a} → {A B : Set a} → A ≡ B → A → B
coerce refl = id
\end{code}

\section{la'oi .\F{resize}.}
ni'o ga jonai la'o zoi.\ \F{\AgdaUnderscore{}++\AgdaUnderscore}\ \OpF \$\ \F{replicate} \B t\ .zoi.\ du ko'a goi la'o zoi.\ \F{resize}\ \Sym\{\AgdaUnderscore\Sym\} \Sym\{\B m\Sym\} \Sym\{\B n\Sym\}\ \B t\ .zoi.\ gi ga je ctaipe la'o zoi.\ \B n\ \OpF{ℕ.≤}\ \B m\ .zoi.\ gi ko'a du la'o zoi.\ \F{drop}\ \OpF \$\ \B m\ \OpF ∸\ \B n\ .zoi.

\begin{code}
resize : ∀ {a} → {m n : ℕ} → {A : Set a}
       → A → Vec A m → Vec A n
resize {_} {m} {n} {A} x xs = xt $ n ℕ.≤? m
  where
  xt : Dec $ n ℕ.≤ m → Vec A n
  xt (yes z) = drop (m ∸ n) $ coerce coc xs
    where
    coc = sym $ cong (Vec A) $ DNP.m∸n+n≡m z
  xt (no z) = padin ++ xs ▹ coerce (cong (Vec A) bitc)
    where
    padin : Vec A $ n ∸ m
    padin = replicate x
    bitc : n ∸ m + m ≡ n
    bitc = DNP.m∸n+n≡m $ DNP.≰⇒≥ z

  open ≡-Reasoning

  -- ni'o la .varik. cu djica ko'a goi lo nu
  -- zoi zoi. resize x xs .zoi. ja zo'e je zo'e cu basti
  -- zoi zoi. xt (yes g) .zoi. je zo'e
  -- .i tu'a la'o zoi. resize x xs .zoi. ja zo'e cu
  -- zmadu tu'a la'o zoi. xt $ yes g .zoi. je zo'e le
  -- ka la .varik. cu jinvi le du'u ce'u sampu kei kei je
  -- le ka frili la .varik. fa lo nu jimpe fi ce'u
  --
  -- .i la .varik. cu jinvi le du'u ko'a se sarcu lo
  -- nu ciksi lo ctaipe be le su'u ga naja ctaipe
  -- lo su'u la'o zoi. m .zoi.* dubjavme'a
  -- la'o zoi. n .zoi. gi la'o zoi. resize x xs .zoi.
  -- du la'o zoi. xt $ yes g .zoi. ja zo'e
  --
  -- * .i pilno le co'e co me zo la'o jenai ke zo la
  -- ja zo'e ki'u le su'u vlaba'u fi zoi glibau.
  -- LATIN MAJUSCULE MIKE .glibau.

  flipko : ∀ {a} → {A B : Set a}
         → (x : A)
         → (d : A ≡ B)
         → x ≡_ $ coerce d x ▹ coerce (sym d)
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
          xs ≡_ $ drop (n ∸ m) $ xt (no g) ▹ coerce sink
  takis g = sym $ begin
    drop (n ∸ m) konk ≡⟨ konkydus ▹ cong (drop $ n ∸ m) ⟩
    drop (n ∸ m) (pad ++ xs) ≡⟨ sym $ dropdus pad xs ⟩
    xs ∎
    where
    pad = replicate x
    k = cong (Vec A) $ DNP.m∸n+n≡m $ DNP.≰⇒≥ g
    konk : Vec A $ n ∸ m + m
    konk = flip coerce (xt $ no g) $ sym k
    konkydus : konk ≡ pad ++ xs
    konkydus = sym $ flipko (pad ++ xs) k
    dropdus : ∀ {a} → {A : Set a} → {m n : ℕ}
            → (x : Vec A m)
            → (z : Vec A n)
            → z ≡ drop (length x) (x ++ z)
    dropdus [] _ = refl
    dropdus (x ∷ xs) z = dropdus xs z ▹ subst (_≡_ _) (d xs z x)
      where
      d = λ x z e → sym $ DVP.unfold-drop (length x) e $ x ++ z
\end{code}

\subsection{le su'u pilno le la'oi .\F{xt}.\ co'e jenai lo zo'oi .\AgdaKeyword{with}.\ co'e}
ni'o lo nu basti ko'a goi le la'oi .\F{xt}.\ co'e cu rinka lo nu nandu fa lo nu ciksi la'oi .\F{flipko}.\ je zo'e

.i ga je ko'a milxe le ka ce'u fegli la .varik.\ gi ku'i la .varik.\ na birti lo du'u ma kau mapti la'oi .\F{flipko}.\ je zo'e je cu mleca ko'a le ka ce'u fegli

.i ranji fa le nu la .varik.\ cu djica curmi lo nu stidi

.i la .varik.\ cu cusku dei ba le nu la .varik.\ cu troci lo nu basygau le zo'oi .\AgdaKeyword{with}.\ co'e ko'a\sds  .i lo du'u tcidu dei cu .indika le du'u fliba

\subsubsection{le se zvati}
ni'o xu cadga fa lo nu dei me'oi .Agda.\ pinka\sds  .i la'oi .\F{resize}.\ du lo ro se srana be ke'a

\section{la .\F{dist}.}
ni'o la'o zoi.\ \F{dist} \Sym ⦃ \B Q \Sym ⦄ \B x \B z \B d\ .zoi.\ nilzilcmi lo'i ro ctaipe be la'o zoi.\ \D{Fin} \OpF \$ \F{LL.l} \B Q \AgdaUnderscore \B x\ .zoi.\ be'o poi lo meirmoi be ke'a bei fo la'oi .\B{x}.\ cu drata lo meirmoi be ke'a bei fo la'oi .\B{x}.

\begin{code}
dist : ∀ {a} → {A : Set a}
     → ⦃ Q : LL A ⦄ → ⦃ Eq $ LL.e Q ⦄
     → (x z : A)
     → LL.l Q x ≡ LL.l Q z
     → ℕ
dist ⦃ Q ⦄ x z d = Vec≤.length $ filter drata $ zipᵥ x' z'
  where
  drata = _≟_ false ∘ isYes ∘ uncurry _≟_
  x' = flip coerce (LL.vec Q x) $ cong (Vec _) d
  z' = LL.vec Q z
\end{code}

\section{la .\F{pausyk}.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu la .varik.\ cu ciksi la .\F{pausyk}.\ bau la .lojban.

\begin{code}
pausyk : (b e : ℕ) → ∃ $ λ n → suc n ≡ suc b ^ e
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
    bizum = _+_ $ b * z₁
    open Relation.Binary.PropositionalEquality.≡-Reasoning
\end{code}

\section{la \F{panci}}
ni'o ga jonai la'oi .\AgdaInductiveConstructor{nothing}.\ du ko'a goi la'o zoi.\ \F{panci} \B k\ .zoi.\ gi ga je ctaipe la'o zoi.\ \F{nu,iork} \B k\ .zoi.\ gi ko'a me'oi .\AgdaInductiveConstructor{just}.\ la .\F{k}.

\begin{code}
panci : ∀ {a} → {A : Set a}
      → ⦃ L : LL A ⦄ → ⦃ Eq $ LL.e L ⦄
      → A → Maybe A
panci v = mapₘ (λ _ → v) $ decToMaybe $ Dec (nu,iork v) ∋ _ ≟ _
\end{code}

\section{la .\F{indice}.}
ni'o ro da poi ke'a ctaipe la'o zoi.\ \D{Fin} \AgdaUnderscore{}\ .zoi.\ zo'u lo meirmoi be da bei fo la'o zoi.\ \F{indice} \B x\ .zoi.\ .orsi li re fo da fi lo meirmoi be da bei fo la'oi .\B{x}.

\begin{code}
indice : ∀ {a} → {A : Set a} → {n : ℕ}
       → Vec A n → flip Vec n $ A × Fin n
indice = flip zipᵥ $ allFin _
\end{code}

\chap{le fancu co ke porsi be lo'i me'oi .bit.\ ke'e}

\section{la'oi .\F{nbits}.}
ni'o ko'a goi la'o zoi.\ \F{nbits} \B q\ .zoi.\ porsi lo'i su'o me'oi .bit.\ poi ke'a pagbu la'oi .\B q.\sds  .i ga je lo pamoi be ko'a cu traji le ka ce'u me'oi .significant.\ kei le ka ce'u zenba gi lo romoi be ko'a cu traji le ka ce'u me'oi .significant.\ kei le ka ce'u mleca

.i la'oi .\F{nbits}.\ simsa la'o zoi.\ \F{Data.Bin.toBits}\ .zoi.\ je ku'i cu me'oi .truncate.

\begin{code}
nbits : {n : ℕ} → ℕ → Vec (Fin 2) n
nbits = resize zero ∘ fromList ∘ reverse ∘ proj₁ ∘ toDigits 2
\end{code}

\section{la'oi .\F{b2f}.}
ni'o la'o zoi.\ \F{toℕ} \OpF \$ \F{b2f} \B x\ .zoi.\ selsni la'oi .\B x.\ noi .endi le me'oi .big.

\begin{code}
b2f : {m n : ℕ} → Vec (Fin $ suc m) n → Fin $ suc m ^ n
b2f {_} {0} _ = zero
b2f {m'} {n@(suc _)} = portenfa ∘ indice ∘ mapᵥ f2f
  where
  m = suc m'
  F = Fin $ suc _
  portenfa : flip Vec n $ F × Fin _ → Fin $ m ^ n
  portenfa = coerce k ∘ foldrᵥ _ (f𝔽 _+_) zero ∘ mapᵥ tefpi'i
    where
    k = cong Fin $ proj₂ $ pausyk m' n
    tefpi'i = uncurry (f𝔽 $ λ a b → a * m ^ b) ∘ map₂ f2f
\end{code}

\subsection{le se zvati}
ni'o xu cadga fa lo nu muvgau le velcki be ko'a goi la'oi .\F{b2f}.\ lo drata be la'au \chapsname\ li'u\sds  .i ko'a mapti lo na ctaipe be ko'e goi la'o zoi.\ \D{Fin} \AgdaNumber 2\ .zoi.\ je ku'i cu co'e ja selbi'o zo'e poi ctaipe ko'e fa lo ro mapti be ke'a\sds  .i la .varik.\ na birti lo du'u ma kau ckupau je cu zmadu la'au \chapsname\ li'u le ka ko'a mapti ce'u

\section{la .\F{cunsof}.}
ni'o la .\F{cunsof}.\ cu me'oi .\F{pure}.\ lo me'oi .pseudorandom.

ni'o zo .cunsof. cmavlaka'i lu cunso .fin. li'u

\begin{code}
cunsof : {n : ℕ} → IO $ Fin $ 2 ^ n
cunsof {n} = b2f ∘ mapᵥ sb2f <$> cunvek n
  where
  sb2f = λ n → if n then suc zero else zero
  cunvek : (n : ℕ) → IO $ Vec Bool n
  cunvek n = resize false ∘ fromList <$> IO.List.sequence (cunste n)
    where
    cunste : ℕ → List $ IO Bool
    cunste = flip _∘_ Data.List.upTo $ map $ const $ IO.lift cunsob
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
ni'o la .varik.\ cu djica lo nu la'oi .\F{cunsof}.\ ctaipe ko'a goi la'o zoi.\ \Sym\{\B n \Sym : \D ℕ\Sym\} \Sym → \D{IO} \OpF \$ \D{Fin} \OpF \$ \AgdaInductiveConstructor{suc} \B n\ .zoi.\ldots kei jenai ku'i cu birti lo du'u ma kau zabna je cu me'oi .Agda.\ velcki lo versiio be la .\F{cunsof}.\ poi ke'a ctaipe ko'a

.i la .varik.\ na djuno lo du'u ma kau filri'a lo nu lo me'oi .Haskell.\ co'e cu benji lo ctaipe be lo mapti be la'o zoi.\ \D{Fin} \B x\ .zoi.\ la'oi .Agda.  .i tu'a la'oi .\xactaipes{Bool}.\ sampu\ldots je ku'i cu mapti la'o zoi.\ \D{Fin} \AgdaNumber 2 .zoi.\ jenai zo'e

.i ji'a ga naja la .\F{cunsof}.\ cu co'e ja binxo lo ctaipe be ko'a gi cadga fa lo nu muvgau lo velcki be la .\F{cunsof}.

.i ku'i ga je ko'e goi zoi zoi.\ \F{cunsof} \Sym = \F{pure} \AgdaInductiveConstructor{zero} .zoi.\ sampu je cu mapti ko'a gi frili fa lo nu jimpe fi ko'e

\section{la'oi .\F{\AgdaUnderscore{}∧𝔹ℕ𝔽\AgdaUnderscore}.}
ni'o la'o zoi.\ \B a \OpF{∧𝔹ℕ𝔽} \B b\ .zoi.\ mu'oi glibau.\ bitwise and .glibau.\ la'oi .\B a.\ la'oi .\B b.

\begin{code}
_∧𝔹ℕ𝔽_ : {n : ℕ} → ℕ → Op₁ $ Fin $ suc n
_∧𝔹ℕ𝔽_ a = toFin ∘ zipWithᵥ (f𝔽 _*_) (nbits a) ∘ nbits ∘ toℕ
  where
  -- | ni'o narcu'i fa lo nu zmadu
  -- .i cumki fa lo nu la'e di'u krinu lo nu cadga fa
  -- lo nu basti lo mu'oi zoi. Data.Fin.fromℕ≤ .zoi. co'e
  --
  -- .i le su'u la .varik. na basygau le pa
  -- lerpinsle le'i ci lerpinsle cu se krinu le
  -- su'u la .varik. cu djica lo nu zvati lo
  -- zabna mapti fa lo pinka be le su'u narcu'i
  toFin : {n : ℕ} → Vec (Fin 2) $ suc n → Fin $ suc n
  toFin = f2f ∘ b2f
\end{code}

\section{la'oi .\F{hw𝕄}.}
ni'o la'o zoi.\ \F{hw𝕄} \B t\ .zoi.\ grisumji lo'i ro co'e poi su'o da poi ke'a xi re co'e ja rajypau la'oi .\B{t}.\ zo'u ke'a mu'oi glibau.\ HAMMING weight .glibau.\ da

\begin{code}
hw𝕄 : {a m n : ℕ} → 𝕄 (Fin a) m n → ℕ
hw𝕄 = sumᵥ ∘ mapᵥ hWV𝔽
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

\paragraph{la'oi .\F{MCParam.F}.}
ni'o la'o zoi.\ \F{MCParam.F} \B q\ .zoi.\ me'oi .monic.\ je me'oi .irreducible.\ cpolynomi'a fi la'o zoi.\ \F{MCParam.t} \B q\ .zoi\ldots je cu co'e

\paragraph{la'oi .\F{MCParam.k}.}
ni'o la'o zoi.\ \F{MCParam.k} \B q\ .zoi.\ me'oi .dimension.\ lo me'oi .code.\ pe la'oi .\B q.

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
ni'o la'au \chapsname\ li'u vasru le velcki be vu'oi le fancu je zo'e vu'o poi tu'a ke'a filri'a lo nu zbasu lo termifckiku

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
  fromList? : _ → _
  fromList? v = mapₘ kofrol $ decToMaybe $ _ ≟ _
    where
    kofrol = λ c → coerce (cong (Vec _) c) $ fromList v
\end{code}

\section{la'oi .\F{FieldOrdering}.}
ni'o \specimp{FieldOrdering}

\begin{code}
FieldOrdering : {p : MCParam}
              → Fin $ MCParam.σ₂ p * MCParam.q p
              → Maybe $ Vec (Fin $ MCParam.q p) $ MCParam.q p
FieldOrdering {p} f = mapₘ α $ sartre $ indice a
  where
  q = MCParam.q p
  v = flip Vec q $ Fin $ MCParam.σ₂ p
  vex = flip Vec q $ Fin (MCParam.σ₂ p) × Fin q
  a : v
  a = {!!}
  α : vex → Vec (Fin q) q
  α = mapᵥ $ λ (a , π) → toFin $ sumᵥ $ mapᵥ (tefpi'i a π) $ allFin m
    where
    m = MCParam.m p
    toFin : ℕ → Fin _
    toFin = {!!}
    -- | ni'o mo la .z.
    -- .i ga naja cpolynomi'a co'e gi na sarcu fa lo nu
    -- pilji  .i nibli la'e di'u fa le su'u ga je co'e gi
    -- pilno la'oi .Vec. tu'a lo cpolinomi'a  .i ku'i la
    -- .varik. na birti ko'a goi le du'u cpolinomi'a co'e
    -- .i ku'i cumki fa lo nu binxo  .i le su'u sampu cu
    -- krinu le su'u la .varik. cu milxe le ka ce'u senpi
    -- ko'a
    tefpi'i = λ a π j → toℕ π * {!!} ^ (m ∸ 1 ∸ toℕ j)
  sartre : vex → Maybe vex
  sartre = mapₘ jort ∘ panci
    where
    -- | ni'o pilno la .jort. lo nu me'oi .lexicographic.
    -- porganzu
    jort : ∀ {a} → {A : Set a} → {m n : ℕ}
         → Op₁ $ flip Vec n $ Fin m × A
    jort = mapᵥ proj₂ ∘ jort' ∘ mapᵥ (λ a → proj₁ a , a)
      where
      jort' : ∀ {a} → {A : Set a} → {n : ℕ} → Op₁ $ Vec (_ × A) n
      jort' = {!!}
\end{code}

\section{la'oi .\F{FixedWeight}.}
ni'o \specimp{FixedWeight}

ni'o \termineidyr{FixedWeight}

\begin{code}
{-# NON_TERMINATING #-}
FixedWeight : {p : MCParam}
            → (IO $ Σ
                (Vec (Fin 2) $ MCParam.n p)
                (λ e → hWV𝔽 e ≡ MCParam.t p))
FixedWeight {p} = cof IO.>>= restart? ∘ FixedWeight'
  where
  OT = ∃ $ λ e → hWV𝔽 e ≡ MCParam.t p
  -- | ni'o cumki fa lo nu cumki fa lo nu tu'a
  -- la'oi .restart?. rinka lo nu na me'oi .terminate.
  restart? : Maybe OT → IO OT
  restart? = maybe pure $ FixedWeight {p}
  -- | ni'o la'o zoi. mceliece.pdf .zoi. vasru le na'e
  -- zabna je velcki be la'oi .τ.  .i la .varik. cu
  -- na birti lo du'u pilji ji kau cu tenfa  .i ku'i la
  -- .varik. cu djuno le du'u na mapti fa le me zo joi se
  -- xamsku
  τ = if MCParam.n p ≡ᵇ MCParam.q p then MCParam.t p else {!!}
  cof = cunsof {MCParam.σ₁ p * τ}
  FixedWeight' : Fin $ 2 ^_ $ MCParam.σ₁ p * τ → Maybe OT
  FixedWeight' b = mapₘ (map₂ proj₁ ∘ e') a?
    where
    d : Vec ℕ τ
    d = mapᵥ (λ j → sumᵥ $ mapᵥ (uijis j) $ allFin _) $ allFin τ
      where
      uijis : Fin τ → Fin $ MCParam.m p → ℕ
      uijis j i = 2 ^ toℕ i *_ $ toℕ $ lookup b' ind
        where
        ind = f2f mind ▹ coerce (cong Fin $ proj₂ sukdiz)
          where
          -- | ni'o zo .mind. cmavlaka'i lu mabla
          -- .indice li'u
          --
          -- ni'o ma zmadu fi le ka ce'u zabna kei fe
          -- le me'oi .fromℕ. co'e noi ke'a pluja je cu
          -- fegli la .varik.
          -- .i xu mleca la'o zoi. MCParam.σ₁ * τ .zoi.
          mind = fromℕ $ toℕ i + MCParam.σ₁ p * toℕ j
          sukdiz : ∃ $ λ n → suc n ≡ MCParam.σ₁ p * τ
          sukdiz = {!!}
        b' = nbits $ toℕ b
    a? : Maybe $ Vec (Fin $ MCParam.n p) $ MCParam.t p
    a? = _>>=ₘ panci $ toVec? $ Data.List.take (MCParam.t p) mlen
      where
      -- | ni'o zo .mlen. cmavlaka'i
      -- lu mleca la .n. li'u
      mlen : List $ Fin $ MCParam.n p
      mlen = Data.List.mapMaybe id $ map mlen? $ toList d
        where
        mlen? = mapₘ fromℕ< ∘ decToMaybe ∘ (ℕ._<? _)
      toVec? : List $ Fin $ MCParam.n p
             → Maybe $ Vec (Fin $ MCParam.n p) $ MCParam.t p
      toVec? l = flip mapₘ dun? $ flip coerce (fromList l) ∘ cong (Vec _)
        where
        dun? = decToMaybe $ _ ≟ _
    e' : (a : _)
       → Σ (Vec (Fin 2) (MCParam.n p)) $ λ e
         → hWV𝔽 e ≡ MCParam.t p
         × let el = Data.List.allFin _ in
           flip Listal.All el $ _≡_ (suc zero) ∘ lookup e ∘ lookup a
    e' = {!!}
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

.i la'o zoi.\ \F{SeededKeyGen} \B p \B δ\ .zoi.\ .orsi li re lo mu'oi glibau.\ Classic MCELIECE .glibau.\ ke sivni termifckiku lo mapti be ko'a

ni'o me'oi .recurse.  .i \termineidyr{SeededKeyGen}

\begin{code}
{-# NON_TERMINATING #-}
SeededKeyGen : {p : MCParam} → Fin $ 2 ^ MCParam.ℓ p → KP p
SeededKeyGen {p} δ = fromMaybe (SeededKeyGen δ') mapti?
    where
    E = MCParam.G p δ
    δ' = b2f $ reverseᵥ $ nbits {MCParam.ℓ p} $ toℕ $ rev E
      where
      rev : {n : ℕ} → Op₁ $ Fin n
      rev = opposite

      module Veritas where
        zivle : {n : ℕ} → (t : Fin n) → t ≡ rev (rev t)
        zivle = {!!}
    mapti? : Maybe $ KP p
    mapti? = (apₘ ∘₂ mapₘ) _,_ (sivni >>=ₘ MatGen) sivni
      where
      sivni = g? >>=ₘ λ (j , lg , g) → just record {
        lg = lg;
        Γ = g , j;
        s = nbits $ toℕ $ b2f $ nbits {n} $ toℕ E
        }
        where
        n = MCParam.n p
        g? : let Vq = Vec $ Fin $ MCParam.q p in
             Maybe $ Vq n × ∃ Vq
        g? = mapₘ (λ g → {!!} , _ , g) $ Irreducible {p} Eₚ
          where
          σ₁*t = λ p → MCParam.σ₁ p * MCParam.t p
          Eₚ = b2f $ drop n $ nbits {n + σ₁*t p} $ toℕ E
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
ni'o la'o zoi.\ \F{Hx} \B p \B T\ .zoi.\ konkatena lo me'oi .identity.\ nacmeimei la'oi .\B{T}.

\begin{code}
Hx : (p : MCParam)
   → Public p
   → 𝕄 (Fin 2) (MCParam.n p) $ MCParam.n-k p
Hx p = coerce (cong nacmeimid n∸k+k≡n) ∘ _∣_ (I zero $ suc zero)
  where
  nacmeimid = λ i → 𝕄 (Fin 2) i $ MCParam.n-k p
  n∸k+k≡n = DNP.m∸n+n≡m $ DNP.m∸n≤m _ $ MCParam.m p * _
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
  v = C₀ ++ replicate zero ▹ coerce kos
    where
    kos : xv (λ p → MCParam.n-k p + MCParam.k p) ≡ xv MCParam.n
    kos = cong (Vec _) $ DNP.m∸n+n≡m k≤n
      where
      k≤n : MCParam.k p ℕ.≤ MCParam.n p
      k≤n = DNP.m∸n≤m _ $ MCParam.m p * MCParam.t p
  c' : Maybe $ ∃ $ λ c → dist c v refl ℕ.≤ MCParam.t p
  c' = {!!}
  c = mapₘ proj₁ c'
  e = flip mapₘ c $ zipWithᵥ (f𝔽 _+_) v
  mapti : xv MCParam.n → Set
  mapti e = ∃ $ _≡_ C₀ ∘ Encode p e bar
  mapti? : xv MCParam.n → Maybe $ ∃ mapti
  mapti? e = mapₘ (e ,_) $ dun? >>=ₘ λ x → mapₘ (x ,_) dun?
    where
    dun? : ∀ {a} → {A : Set a} → {B C : A}
         → ⦃ Eq A ⦄
         → Maybe $ B ≡ C
    dun? = decToMaybe $ _ ≟ _
\end{code}
\end{document}
