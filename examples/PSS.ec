require import Fun.
require import Int.
require import Real.
require import FSet.
require import Map.
require import Pair.
require import Distr.

(*** These belong somewhere else *)
op pi3_1 (t:'a * 'b * 'c): 'a =
  let (a,b,c) = t in a.

op pi3_2 (t:'a * 'b * 'c): 'b =
  let (a,b,c) = t in b.

op pi3_3 (t:'a * 'b * 'c): 'c =
  let (a,b,c) = t in c.

(*** General definitions *)
(** Lengths *)
op k:int.
axiom lt0_k: 0 < k.

op k0:int.
axiom lt0_k0: 0 < k0.

op k1:int.
axiom lt0_k1: 0 < k1.

axiom constraints:
  k0 + k1 < k - 1.

op kg:int = k - k1 - 1.
lemma lt0_kg1: 0 < kg by [].

op kg2:int = k - k0 - k1 - 1.
lemma lt0_kg2: 0 < kg2 by [].

op k':int = k - 1.
lemma lt0_k': 0 < k' by [].

op qS:int.
axiom leq0_qS: 0 <= qS.

op qH:int.
axiom leq0_qH: 0 <= qH.

op qG:int.
axiom leq0_qG: 0 <= qG.

(** Types *)
require AWord.
require import ABitstring.

type message = bitstring.

(* Signatures *)
type signature.
clone import AWord as Signature with
  type word <- signature,
  op length <- k.

(* Nonce *)
type salt.
clone import AWord as Salt with
  type word <- salt,
  op length <- k0.
op sample_salt = Salt.Dword.dword.
axiom saltL: mu sample_salt cpTrue = 1%r.

(* Output of H *)
type htag.
clone import AWord as HTag with
  type word <- htag,
  op length <- k1.
op sample_htag = HTag.Dword.dword.
axiom htagL: mu sample_htag cpTrue = 1%r.

(* Output of G *)
type gtag.
clone import AWord as GTag with
  type word <- gtag,
  op length <- kg.
op sample_gtag = GTag.Dword.dword.
axiom gtagL: mu sample_gtag cpTrue = 1%r.

(* Output of G2 [G1 produces an HTag] *)
type g2tag.
clone import AWord as G2Tag with
  type word <- g2tag,
  op length <- kg2.

(* Domain of RSA *)

(** Instantiating *)
require PKS.
require OW.
require RandomOracle.

type pkey.
type skey.
op keypairs: (pkey * skey) distr.

op sample_plain: pkey -> signature distr.

clone import OW as RSA with
  type pkey <- pkey,
  type skey <- skey,
  type t <- signature,
  op keypairs <- keypairs,
  op challenge <- sample_plain.

lemma plainL pk: weight (sample_plain pk) = 1%r.
proof strict.
rewrite /weight; apply Antisymm.
  by cut [_ H]:= mu_bounded (sample_plain pk) cpTrue.
  apply (Trans _ (mu (sample_plain pk) (f_dom pk))).
    by rewrite f_dom_challenge.
    by apply mu_sub=> x; rewrite /cpTrue.
qed.

axiom f_dom_rng pk: valid_pkey pk => f_dom pk = f_rng pk.
axiom finv_dom_rng sk: valid_skey sk => finv_dom sk = finv_rng sk.

op modulus_p: pkey -> int.
axiom modulus_size pk sk:
  valid_keys (pk,sk) => 2^(k-1) <= modulus_p pk < 2^k.

op inv: signature -> pkey -> signature.
op ( * ): signature -> signature -> pkey -> signature.

axiom mulC (x y:signature) pk:
  f_dom pk x =>
  f_dom pk y =>
  (x * y) pk = (y * x) pk.

op one_sig: signature.

axiom mul_one (x:signature) pk:
  f_dom pk x =>
  (x * one_sig) pk = x.

axiom mul_inv (x:signature) pk:
  x <> Signature.zeros =>
  f_dom pk x =>
  (x * (inv x pk)) pk = one_sig.

axiom homo_f_mul (x y:signature) pk:
  f_dom pk x =>
  f_dom pk y =>
  f pk ((x * y) pk) = (f pk x * f pk y) pk.

axiom homo_finv_mul (x y:signature) pk sk:
  valid_keys (pk,sk) =>
  finv_dom sk x =>
  finv_dom sk y =>
  finv sk ((x * y) pk) = (finv sk x * finv sk y) pk.

axiom f_zero pk: valid_pkey pk => f pk Signature.zeros = Signature.zeros.
axiom f_one sk: valid_skey sk => finv sk (one_sig) = one_sig.

clone import RandomOracle.LazyEager as Gt with
  type from <- htag,
  type to <- gtag,
  op dsample <- sample_gtag.
module G = Gt.Lazy.RO.
module G' = Gt.Eager.RO.

clone import RandomOracle.Lazy as Ht with
  type from <- (message * salt),
  type to <- htag,
  op dsample <- sample_htag.
module H = Ht.RO.

clone import PKS as PKSi with
  type pkey <- pkey,
  type skey <- skey,
  type message <- message,
  type signature <- signature.
import EF_CMA.

(*** Defining PSS *)
module PSS(G:Gt.Types.Oracle,H:Ht.Types.Oracle): Scheme = {
  fun init(): unit = {
    G.init();
    H.init();
  }

  fun g1(x:htag):salt = {
    var r:gtag;
    r  = G.o(x);
    return Salt.from_bits (sub (to_bits r) 0 k0);
  }

  fun g2(x:htag):g2tag = {
    var r:gtag;
    r  = G.o(x);
    return G2Tag.from_bits (sub (to_bits r) k0 kg2);
  }

  (* Keygen *)
  fun keygen():(pkey * skey) = {
    var (pk, sk):(pkey * skey);
    (pk,sk) = $keypairs;
    return (pk,sk);
  }

  (* Sign *)
  fun sign(sk:skey, m:message):signature = {
    var r:salt;
    var rMask:salt;
    var maskedR:salt;
    var w:htag;
    var gamma:g2tag;
    var y:signature;

    r = $sample_salt;
    w  = H.o((m,r));
    rMask  = g1(w);
    maskedR = rMask ^ r;
    gamma  = g2(w);
    y = Signature.from_bits (zeros 1 || (to_bits w) || (to_bits maskedR) || (to_bits gamma));
    return (finv sk y); (* For fault injection, we will later refine this; we should make it a function so it can be reasoned about separately *)
  }

  (* Verify *)
  fun verify(pk:pkey, m:message, s:signature):bool = {
    var y:signature;
    var w:htag;
    var w':htag;
    var maskedR:salt;
    var gamma:g2tag;
    var gamma':g2tag;
    var rMask:salt;
    var r:salt;
    var b:bool;

    y = (f pk s);
    b = (sub (to_bits y) 0 1 <> zeros 1);
    w = HTag.from_bits (sub (to_bits y) 1 k1);
    maskedR = Salt.from_bits (sub (to_bits y) (k1 + 1) k0);
    gamma = G2Tag.from_bits (sub (to_bits y) (k1 + k0 + 1) kg2);
    rMask  = g1(w);
    r = rMask ^ maskedR;
    w'  = H.o((m,r));
    gamma'  = g2(w);
    return (w = w' /\ gamma = gamma' /\ !b);
  }
}.

(* A CMA adversary with access to two random oracles *)
module type CMA_2RO(G:Gt.Types.ARO,H:Ht.Types.ARO,S:AdvOracles) = {
  fun forge(pk:pkey): message * signature {* G.o H.o S.sign}
}.

section. 
  declare module A:CMA_2RO {G,G',H,EF_CMA,Wrap,OW}.
  axiom adversaryL (G <: Gt.Types.ARO {A}) (H <: Ht.Types.ARO {A}) (S <: AdvOracles {A}):
    islossless G.o => islossless H.o => islossless S.sign =>
    islossless A(G,H,S).forge.

  (* This is the memory that is used by the concrete adversary during the proof *)
  (* In the final transition, we rewrite the concrete adversary into an
     adversary against OW, and therefore drop the secret key from its state.    *)
  local module Mem = {
    var pk:pkey
    var sk:skey
    var qs:message set

    fun init(ks:pkey * skey): unit = {
      (pk,sk) = ks;
      qs = FSet.empty;
    }
  }.

  module type SplitOracle = {
    fun init(ks:pkey*skey): unit { * }
    fun o(c:bool,x:message * salt):htag
  }.

  (** Since the proof mostly works by modifying H,
      with some eager-style interactions with G,
      we will mostly reason in terms of a concrete
      adversary trying to distinguish various
      implementations of G and H through the signing
      oracle. This should allow some abstraction in the
      proof, and in particular in the two eager steps
      on G.                                             **)
  module type Gadv (H:SplitOracle, G:Gt.Types.ARO) = { 
    fun main (ks:pkey * skey) : bool {* H.o G.o}
  }.

  local module Gen (Gadv:Gadv, H:SplitOracle, G:Gt.Types.Oracle) = {
    module GA = Gadv(H,G)
    fun main () : bool = { 
      var keys : pkey * skey;
      var b : bool;
      keys = $keypairs;
      G.init();
      H.init(keys);
      b = GA.main(keys);
      return b;
    }
  }.

  local module GAdv(H:SplitOracle, G:Gt.Types.ARO) = {
    (* Wrapping a split oracle for use by the signing oracle *)
    module Hs = {
      fun o(x:message * salt): htag = {
        var r:htag;
        r = H.o(false,x);
        return r;
      }
    }

    (* Wrapping a split oracle for direct use by the adversary *)
    module Ha = {
      fun o(x:message * salt): htag = {
        var r:htag;
        r = H.o(true,x);
        return r;
      }
    }

    (* Signing oracle *)
    module S = {
      fun sign(m:message): signature = {
        var r:salt;
        var g:gtag;
        var rMask:salt;
        var maskedR:salt;
        var w:htag;
        var gamma:g2tag;
        var y:signature;

        Mem.qs = add m Mem.qs;
        r = $sample_salt;
        w = Hs.o((m,r));
        g = G.o(w);
        rMask = Salt.from_bits (sub (to_bits g) 0 k0);
        maskedR = rMask ^ r;
        gamma = G2Tag.from_bits (sub (to_bits g) k0 kg2);
        y = Signature.from_bits (zeros 1 || (to_bits w) || (to_bits maskedR) || (to_bits gamma));
        return finv Mem.sk y;
      }

      fun fresh(m:message): bool = {
        return !mem m Mem.qs;
      }
    }

    module A = A(G, Ha, S)

    fun main (ks:pkey*skey) : bool = { 
      var m:message;
      var s:signature;
      var y:signature;
      var w:htag;
      var w':htag;
      var g:gtag;
      var maskedR:salt;
      var gamma:g2tag;
      var gamma':g2tag;
      var rMask:salt;
      var r:salt;
      var forged, fresh:bool;

      Mem.init(ks);
      (m,s) = A.forge(Mem.pk);

      y = (f Mem.pk s);
      forged = (sub (to_bits y) 0 1 <> zeros 1);
      w = HTag.from_bits (sub (to_bits y) 1 k1);
      maskedR = Salt.from_bits (sub (to_bits y) (k1 + 1) k0);
      gamma = G2Tag.from_bits (sub (to_bits y) (k1 + k0 + 1) kg2);
      g = G.o(w);
      rMask = Salt.from_bits (sub (to_bits g) 0 k0);
      r = rMask ^ maskedR;
      w' = Hs.o((m,r));
      gamma' = G2Tag.from_bits (sub (to_bits g) k0 kg2);
      forged =  w = w' /\ gamma = gamma' /\ !forged;

      fresh = S.fresh(m);
      return forged /\ fresh;
    }
  }.

  local lemma lossless_GAdv (H <: SplitOracle {GAdv}) (G <: Gt.Types.ARO {GAdv}):
    islossless H.o => islossless G.o => islossless GAdv(H, G).main.
  proof strict.
  intros=> HL GL; fun.
  call (_: true ==> true); first by fun.
  wp; call (_: true ==> true); first by fun; call HL.
  wp; call GL.
  wp; call (adversaryL G (<: GAdv(H,G).Ha) (<: GAdv(H,G).S) _ _ _)=> //.
    by fun; call HL.
    fun; wp.
      call GL.
      call (_: true ==> true); first by fun; call HL.
      by rnd; wp; skip; smt.
    by call (_: true ==> true);
      first by fun; wp.
  qed.

  (** A module to store the globals used
      in most variants of H, along with
      some useful equality predicates *)
  local module Hmem = {
    var pk:pkey
    var sk:skey
    var xstar:signature

    fun init(ks:pkey*skey): unit = {
      (pk,sk) = ks;
      xstar = $sample_plain pk;
    }
  }.

  local module Hmap = {
    var m:(message * salt,htag * bool * signature) map

    fun init(ks:pkey*skey) : unit = {
      Hmem.init(ks);
      m = Map.empty;
    }
  }.

  local equiv Hmem_init:
    Hmem.init ~ Hmem.init: ={ks} /\ valid_keys ks{2} ==>
                           ={glob Hmem} /\ valid_keys (Hmem.pk,Hmem.sk){2}
  by (fun; rnd; wp; skip; smt).

  local equiv Hmap_init:
    Hmap.init ~ Hmap.init: ={ks} /\ valid_keys ks{2} ==>
                           ={glob Hmap} /\ valid_keys (Hmem.pk,Hmem.sk){2}
  by (by fun; wp; call Hmem_init).

  pred (=<=) (m0:(message * salt,htag) map) (m1:(message * salt,htag * bool * signature) map) =
    forall x, m0.[x] = if m1.[x] = None then None else Some (pi3_1 (proj m1.[x])).

  (** Zeroth Transition:
      We rewrite PSS into an adversary against Gen with G and a trivial split oracle H0. *)
  local module H0 : SplitOracle = { 
    fun init(ks:pkey*skey): unit = {
      Hmap.init(ks);
    }

    fun o(c:bool,x:message * salt):htag = {
      var r : htag;
      r = $sample_htag;
      if (!in_dom x Hmap.m) Hmap.m.[x] = (r,c,Signature.ones);
      return pi3_1 (proj Hmap.m.[x]);
    }
  }.

  local module G0 = Gen(GAdv,H0,G).

  local equiv PSS_G0_H:
    H.o ~ H0.o: ={x} /\ H.m{1} =<= Hmap.m{2} ==> ={res} /\ H.m{1} =<= Hmap.m{2}.
  proof strict.
  by fun; inline H0.o; wp; rnd; wp; skip; rewrite /(=<=); progress=> //; smt.
  qed.

  (* More informed use of conseq* might speed up some of the smt calls *)
  local equiv PSS_G0:
    EF_CMA(Wrap(PSS(G,H)),A(G,H)).main ~ G0.main: true ==> ={res}.
  proof strict.
  fun; inline G0.main Gen(GAdv,H0,Gt.Lazy.RO).GA.main; wp.
  call (_: ={m} /\ Wrap.qs{1} = Mem.qs{2} ==> ={res});
    first by fun; eqobs_in.
  (* In the following, we would really like to be able to write Ht.RO instead of RO,
     for symmetry and ease of reading. This currently does not work. *)
  inline Wrap(PSS(Gt.Lazy.RO,RO)).verify PSS(Gt.Lazy.RO,RO).verify
         PSS(Gt.Lazy.RO,RO).g1 PSS(Gt.Lazy.RO,RO).g2.
  swap{1} [18..19] -3. (* Grouping the two calls to G on the left *)
  inline GAdv(H0,Gt.Lazy.RO).Hs.o; wp; call PSS_G0_H.
  (* We use seq to cut out the calls to G and limit the scope of the rcond call *)
  wp; seq 12 11: (={glob G, w, m, maskedR, gamma} /\
                  H.m{1} =<= Hmap.m{2} /\
                  Wrap.qs{1} = Mem.qs{2} /\
                  b0{1} = forged{2} /\
                  m1{1} = m{2}).
    wp; inline Wrap(PSS(Gt.Lazy.RO,RO)).init PSS(Gt.Lazy.RO,RO).init
               RO.init Gt.Lazy.RO.init PSS(Gt.Lazy.RO,RO).keygen
               H0.init H.init Mem.init.
    call (_: ={glob G} /\ H.m{1} =<= Hmap.m{2} /\ Wrap.qs{1} = Mem.qs{2} /\ Wrap.sk{1} = Mem.sk{2}).
     by conseq* (_: ={glob G, x} ==> ={glob G, res})=> //; fun; eqobs_in.
     fun*; inline GAdv(H0,Gt.Lazy.RO).Ha.o; sp; wp; call PSS_G0_H=> //.
     fun; inline PSS(Gt.Lazy.RO, RO).sign.
       wp; inline PSS(Gt.Lazy.RO, RO).g1 PSS(Gt.Lazy.RO, RO).g2 Gt.Lazy.RO.o
                  GAdv(H0, Gt.Lazy.RO).Hs.o.
       rcondf{1} 16;
         first intros=> &m; inline RO.o; do !(rnd; wp); skip; progress=> //; smt.
       wp; rnd{1} (cpTrue).
       wp; rnd.
       wp; call PSS_G0_H.
       wp; rnd.
       wp; skip; smt.
    inline Hmap.init Hmem.init; wp; rnd{2} (cpTrue).
    by wp; rnd; wp; skip; progress=> //; smt.

  inline Gt.Lazy.RO.o; rcondf{1} 9.
    by intros=> &m //=; do !(rnd; wp); skip; progress=> //; smt.
    by wp; rnd{1} (cpTrue); wp; rnd; wp; skip; progress=> //; smt.
  qed.

  (** First Transition: Calling G inside H *)
  (* The proof is by two instances of eager,
     where we build a distinguishing adversary
     against G from parameterized versions of
     H0 and H1, and any GAdv. *)
  local module H1 = {
    fun init(ks:pkey * skey): unit = {
      Hmap.init(ks);
    }


    fun o(c:bool, x:message * salt): htag = {
      var w:htag;
      var st:gtag;

      if (!in_dom x Hmap.m) {
        w = $sample_htag;
        Hmap.m.[x] = (w,c,Signature.ones);
        st = G.o(w);
      }
      return pi3_1 (proj Hmap.m.[x]);
    }
  }.

  local module G1 = Gen(GAdv,H1,G).

  module type PSplitOracle (G:Gt.Types.ARO) = {
    fun init(ks:pkey * skey): unit {*}
    fun o(c:bool,x:message * salt): htag {* G.o}
  }.

  local module H0' (G:Gt.Types.ARO) = {
    fun init(ks:pkey*skey): unit = {
      Hmap.init(ks);
    }

    fun o(c:bool,x:message * salt):htag = {
      var r : htag;
      r = $sample_htag;
      if (!in_dom x Hmap.m) Hmap.m.[x] = (r,c,Signature.ones);
      return pi3_1 (proj Hmap.m.[x]);
    }
  }.

  local module H1' (G:Gt.Types.ARO) = {
    fun init(ks:pkey * skey): unit = {
      Hmap.init(ks);
    }


    fun o(c:bool, x:message * salt): htag = {
      var w:htag;
      var st:gtag;

      if (!in_dom x Hmap.m) {
        w = $sample_htag;
        Hmap.m.[x] = (w,c,Signature.ones);
        st = G.o(w);
      }
      return pi3_1 (proj Hmap.m.[x]);
    }
  }.

  local module D (Ga:Gadv, H:PSplitOracle, G:Gt.Types.ARO) = {
    module H = H(G)
    module Ga = Ga(H,G)

    fun distinguish(): bool = {
      var b:bool;
      var ks:pkey * skey;
      ks = $keypairs;
      H.init(ks);
      b = Ga.main(ks);
      return b;
    }
  }.

  local equiv G0_D0 (Ga <: Gadv {G,Hmap}):
    Gen(Ga,H0,G).main ~ Gt.IND(G,D(Ga,H0')).main: true ==> ={res}.
  proof strict.
  by fun;
     inline IND(Lazy.RO,D(Ga,H0')).D.distinguish; swap{1} 1 1;
     eqobs_in.
  qed.

  local equiv D0_D0e (Ga <: Gadv {G,G'}):
    Gt.IND(G,D(Ga,H0')).main ~ Gt.IND(G',D(Ga,H0')).main: true ==> ={res}
  by (apply (eagerRO (D(Ga,H0')) _); apply gtagL).

  local equiv D0e_D1e (Ga <: Gadv {G',Hmap}):
    Gt.IND(G',D(Ga,H0')).main ~ Gt.IND(G',D(Ga,H1')).main: true ==> ={res}.
  proof strict.
  fun.
  call (_: ={glob Eager.RO} /\ forall x, in_dom x G'.m{1}).
    call (_: ={glob Eager.RO, glob Hmap} /\ forall x, in_dom x G'.m{1}).
      (* H *)
      fun; case (in_dom x Hmap.m){1}.
        rcondf{1} 2; first by intros=> &m; rnd.
        by rcondf{2} 1; last wp; rnd{1}; skip; smt.
        rcondt{1} 2; first by intros=> &m; rnd.
        by rcondt{2} 1; last inline Eager.RO.o; wp; rnd; skip; smt.
      (* G *)
      conseq* (_: ={glob G', x} ==> ={glob G', res}); first 2 smt.
        fun; eqobs_in.
    call (_: ={ks} ==> ={glob Hmap}); first by fun; inline H0.init; eqobs_in.
    rnd; skip; smt.
  inline Eager.RO.init;
  while (={work, Eager.RO.m} /\ forall x, !mem x work{1} => in_dom x Eager.RO.m{1}).
    by wp; rnd; wp; skip; progress=> //; smt.
  by wp; skip; smt.
  qed.

  local equiv D1e_D1 (Ga <: Gadv {G,G'}):
    Gt.IND(G',D(Ga,H1')).main ~ Gt.IND(G,D(Ga,H1')).main: true ==> ={res}.
  proof strict.
  by symmetry;
     (* Note that we cannot apply the lemma directly because 'res{2} = res{1}' does not match '={res}' *)
     conseq* (eagerRO (D(Ga,H1')) _)=> //;
     apply gtagL.
  qed.

  local equiv D1_G1 (Ga <: Gadv {G,Hmap}):
    Gt.IND(G,D(Ga,H1')).main ~ Gen(Ga,H1,G).main: true ==> ={res}.
  proof strict.
  by fun;
     inline IND(Lazy.RO,D(Ga,H1')).D.distinguish; swap{1} 1 1;
     eqobs_in.
  qed.

  local equiv G0_G1_abstract (Ga <: Gadv {G,G',Hmap}):
    Gen(Ga,H0,G).main ~ Gen(Ga,H1,G).main: true ==> ={res}.
  proof strict.
  bypr (res{1}) (res{2})=> // a &1 &2 h {h}.
  apply (eq_trans _ Pr[Gt.IND(G,D(Ga,H0')).main() @ &1: a = res]);
    first by equiv_deno (G0_D0 Ga).
  apply (eq_trans _ Pr[Gt.IND(G',D(Ga,H0')).main() @ &1: a = res]);
    first by equiv_deno (D0_D0e Ga).
  apply (eq_trans _ Pr[Gt.IND(G',D(Ga,H1')).main() @ &1: a = res]);
    first by equiv_deno (D0e_D1e Ga).
  apply (eq_trans _ Pr[Gt.IND(G,D(Ga,H1')).main() @ &1: a = res]);
    first by equiv_deno (D1e_D1 Ga).
  by equiv_deno (D1_G1 Ga).
  qed.

  local equiv G0_G1_equiv: G0.main ~ G1.main: true ==> ={res}
  by apply (G0_G1_abstract GAdv).

  local lemma G0_G1 &m:
    Pr[G0.main() @ &m: res] = Pr[G1.main() @ &m: res]
  by equiv_deno G0_G1_equiv.

  (** G2: upto "having already called G on the same w that has just been freshly sampled by H"
        + optimistic sampling *)
  local module H2 = {
    var bad:bool

    fun init(ks:pkey*skey): unit = {
      Hmap.init(ks);
      bad = false;
    }  

    fun o (c:bool, x:message * salt): htag = {
      var w:htag;
      var st:gtag;

      if (!in_dom x Hmap.m) {
        w = $sample_htag;
        st = $sample_gtag;
        Hmap.m.[x] = (w,c,Signature.ones);
        bad = bad \/ in_dom w G.m;
        G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
      }
      return pi3_1 (proj Hmap.m.[x]);
    }
  }.

  local module G2 = Gen(GAdv, H2, G).

  local equiv G1_G2_H:
    H1.o ~ H2.o:
      !H2.bad{2} /\ ={glob Hmap, glob G, c, x} ==>
      !H2.bad{2} => ={glob Hmap, glob G, res}.
  proof strict.
  by fun; if=> //; inline G.o; swap{1} 4 -2; wp;
          rnd ((^) (GTag.from_bits (to_bits (snd x{2}) || zeros (kg - k0))));
          rnd; skip; progress=> //; smt.
  qed.

  local lemma G1_G2_abstract (Ga <: Gadv {G, H1, H2}):
    (forall (H <: SplitOracle{Ga}) (G <: Gt.Types.ARO{Ga}),
       islossless H.o => islossless G.o => islossless Ga(H,G).main) => 
    equiv [Gen(Ga,H1,G).main ~ Gen(Ga,H2,G).main: true ==> !H2.bad{2} => ={res}].
  proof strict.  
  intros=> GaL; fun.
  call (_: H2.bad, ={glob G, glob Hmap}).
    (* H *)
    by conseq* G1_G2_H; smt.
    intros=> _ _; fun.
      if=> //;
      call (Gt.Lazy.lossless_o _);
        first by apply gtagL.
      by wp; rnd; skip; progress=> //; apply htagL.
    intros=> _; fun.
      by if => //; wp; do !rnd cpTrue;
         skip; smt.
    (* G *)
    by conseq* (_: ={glob G, x} ==> ={glob G, res})=> //;
       fun; eqobs_in.
    by intros=> _ _;
       conseq* (Gt.Lazy.lossless_o _);
       apply gtagL.
    by intros=> _ /=;
       conseq* (Gt.Lazy.lossless_o _);
       apply gtagL.
  call (_: ={ks} /\ valid_keys ks{1} ==> ={glob Hmap} /\ !H2.bad{2});
    first by fun; wp; call Hmap_init.
  call (_: true ==> ={glob G});
    first by fun; eqobs_in.
  by rnd; skip; smt.
  qed.

  local equiv G1_G2_equiv: G1.main ~ G2.main: true ==> !H2.bad{2} => ={res}
  by (apply (G1_G2_abstract GAdv); apply lossless_GAdv).

  (** TODO: bound the probability of bad in G2. *)

  (** G3: upto "H is called by the signature oracle on a message * salt pair that has
                previously been queries directly by the adversary" *)
  local module H3: SplitOracle = {
    var bad:bool

    fun init(ks:pkey*skey): unit = {
      Hmap.init(ks);
      bad = false;
    }

    fun o(c:bool,x:message * salt): htag = {
      var w:htag;
      var st:gtag;

      if (!in_dom x Hmap.m) {
        w = $sample_htag;
        st = $sample_gtag;
        Hmap.m.[x] = (w,c,Signature.ones);
        G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
      } else {
        if (!c /\ pi3_2 (proj Hmap.m.[x])) {
          bad = true;
          Hmap.m.[x] = (HTag.zeros,c,Signature.ones);
        }
      }
      return pi3_1 (proj Hmap.m.[x]);
    }
  }.

  local module G3 = Gen(GAdv, H3, G).

  (** Proofs *)
  local equiv G2_G3_H:
    H2.o ~ H3.o:
      !H3.bad{2} /\ ={glob Hmap, glob G, c, x} ==>
      !H3.bad{2} => ={glob Hmap, glob G, res}.
  proof strict.
  fun; sp; if=> //.
    by wp; do !rnd.
    by wp.
  qed.

  local lemma G2_G3_abstract (Ga <: Gadv {H2,H3,G,Hmem}):
    (forall (H <: SplitOracle{Ga}) (G <: Gt.Types.ARO{Ga}),
       islossless H.o => islossless G.o => islossless Ga(H,G).main) => 
    equiv [Gen(Ga,H2,G).main ~ Gen(Ga,H3,G).main: true ==> !H3.bad{2} => ={res}].
  proof strict.
  intros=> GaL; fun.
  call (_: H3.bad, ={glob Hmap, glob G}).
    (* H *)
    by conseq* G2_G3_H=> //; smt.
    by intros=> &2 _; conseq* (_: true ==> true)=> //;
       fun; if=> //; wp; do !rnd cpTrue; skip; smt.
    by intros=> _; fun; if=> //; wp; try (do !rnd cpTrue); skip; smt.
    (* G *)
    by conseq* (_: _ ==> ={glob G, res})=> //; fun; eqobs_in.
    by intros _ _; conseq* (Gt.Lazy.lossless_o _); apply gtagL.
    by intros _; conseq* (Gt.Lazy.lossless_o _); apply  gtagL.
  call (_: ={ks} /\ valid_keys ks{2} ==> ={glob Hmap} /\ !H3.bad{2});
    first by fun; wp; call Hmap_init.
  call (_: true ==> ={glob G});
    first by fun; eqobs_in.
  by rnd; skip; smt.
  qed.

  local equiv G2_G3: Gen(GAdv,H2,G).main ~ Gen(GAdv,H3,G).main : true ==> !H3.bad{2} => ={res}.
  proof strict.
  by apply (G2_G3_abstract GAdv _); apply lossless_GAdv.
  qed.

  (** TODO: Bound the probability of bad in G5 *)

  (** G4: compute z and u from the sampled values
        Note: z is uniform in "bitstrings of length k starting with a zero bit" (denoted '0 || 2^k-1'), and
              u is uniform in f^-1(0 || 2^k-1) *)
  local module H4: SplitOracle = {
    fun init(ks:pkey * skey): unit = {
      Hmap.init(ks);
    }

    fun o(c:bool,x:message * salt): htag = {
      var w:htag;
      var st:gtag;
      var z, u:signature;

      if (!in_dom x Hmap.m)
      {
        w = $sample_htag;
        st = $sample_gtag;
        z = Signature.from_bits (zeros 1 || to_bits w || to_bits st);
        u = if c then ((inv Hmem.xstar Hmem.pk) * finv Hmem.sk  z) Hmem.pk else finv Hmem.sk z;
        Hmap.m.[x] = (w,c,u);
        G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
      }
      else
      {
        if (!c /\ pi3_2 (proj Hmap.m.[x])) Hmap.m.[x] = (HTag.zeros,c,Signature.ones);
      }
      return pi3_1 (proj Hmap.m.[x]);
    }
  }.

  local module G4 = Gen(GAdv,H4,G).

  local equiv G3_G4_H: H3.o ~ H4.o:
    ={glob Hmem, glob G, c, x} /\
    dom Hmap.m{1} = dom Hmap.m{2} /\
    (forall x, in_dom x Hmap.m{1} =>
       pi3_1 (proj Hmap.m.[x]{1}) = pi3_1 (proj Hmap.m.[x]{2})) /\
    (forall x, in_dom x Hmap.m{1} =>
       pi3_2 (proj Hmap.m.[x]{1}) = pi3_2 (proj Hmap.m.[x]{2})) ==>
    ={glob Hmem, glob G, res} /\
    dom Hmap.m{1} = dom Hmap.m{2} /\
    (forall x, in_dom x Hmap.m{1} =>
       pi3_1 (proj Hmap.m.[x]{1}) = pi3_1 (proj Hmap.m.[x]{2})) /\
    (forall x, in_dom x Hmap.m{1} =>
       pi3_2 (proj Hmap.m.[x]{1}) = pi3_2 (proj Hmap.m.[x]{2})).
  proof strict.
  fun;
  if; first smt.
    seq 2 4: (={glob Hmem, glob G, c, x, w, st} /\
              dom Hmap.m{1} = dom Hmap.m{2} /\
              (forall x, in_dom x Hmap.m{1} =>
                pi3_1 (proj Hmap.m.[x]{1}) = pi3_1 (proj Hmap.m.[x]{2})) /\
              (forall x, in_dom x Hmap.m{1} =>
                pi3_2 (proj Hmap.m.[x]{1}) = pi3_2 (proj Hmap.m.[x]{2}))).
      by wp; do !rnd; skip; progress=> //; smt.
    seq 1 1: (={glob Hmem, glob G, c, x, w, st} /\
              dom Hmap.m{1} = dom Hmap.m{2} /\
              (forall x, in_dom x Hmap.m{1} =>
                pi3_1 (proj Hmap.m.[x]{1}) = pi3_1 (proj Hmap.m.[x]{2})) /\
              (forall x, in_dom x Hmap.m{1} =>
                pi3_2 (proj Hmap.m.[x]{1}) = pi3_2 (proj Hmap.m.[x]{2}))).
      wp; skip; progress=> //; first 2 smt.
        by case (x{2} = x0); smt.
    by wp; skip; progress=> //; smt.

    by if; [smt | | ]; wp; skip; progress=> //; smt.  
  qed.

  local equiv G3_G4_abstract (Ga <: Gadv {H2,H3,G,Hmem}):
    Gen(Ga,H3,G).main ~ Gen(Ga,H4,G).main: true ==> ={res}.
  proof strict.
  fun; call (_: ={glob Hmem, glob G} /\
                dom Hmap.m{1} = dom Hmap.m{2} /\
                (forall x, in_dom x Hmap.m{1} =>
                  pi3_1 (proj Hmap.m.[x]{1}) = pi3_1 (proj Hmap.m.[x]{2})) /\
                (forall x, in_dom x Hmap.m{1} =>
                  pi3_2 (proj Hmap.m.[x]{1}) = pi3_2 (proj Hmap.m.[x]{2}))).
    (* H *)
    by conseq* G3_G4_H; smt.
    (* G *)
    conseq* (_: ={glob G, x} ==> ={glob G, res}); first 2 smt.
      by fun; eqobs_in.
  call (_: ={ks} /\ valid_keys ks{1} ==> ={glob Hmap});
    first by fun; wp; call Hmap_init.
  call (_: true ==> ={glob G});
    first by fun; eqobs_in.
  by rnd.
  qed.

  local equiv G3_G4: G3.main ~ G4.main: true ==> ={res}
  by apply (G3_G4_abstract GAdv).

  (** G5: No longer using sk to simulate the oracles *)
  local module H5: SplitOracle = {
    var bad:bool

    fun init(ks:pkey * skey): unit = {
      Hmap.init(ks);
      bad = false;
    }

    fun o(c:bool,x:message * salt): htag = {
      var b:bool = true;
      var i:int = 0;
      var w:htag;
      var st:gtag;
      var z, u:signature;

      if (!in_dom x Hmap.m)
      {
        while (i < kg2 && b)
        {
          u = $sample_plain Hmem.pk;
          z = if c then (f Hmem.pk Hmem.xstar * f Hmem.pk u) Hmem.pk else f Hmem.pk u;
          b = (sub (to_bits z) 0 1 = ones 1);
          w = HTag.from_bits (sub (to_bits z) 1 k1);
          st = GTag.from_bits (sub (to_bits z) (k1 + 1) (kg));
          i = i + 1;
          if (!b)
          {
            Hmap.m.[x] = (w,c,u);
            G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
          }
        }
        bad = bad \/ b;
      }
      else
      {
        if (!c /\ pi3_2 (proj Hmap.m.[x])) Hmap.m.[x] = (HTag.zeros,c,Signature.ones);
      }
      return pi3_1 (proj Hmap.m.[x]);
    }
  }.

  local module G5 = Gen(GAdv,H5,G).

  (** Reduction to OW: no longer using xstar to simulate the oracles *)
  local module I: Inverter = {
    var ystar:signature
    var pk:pkey

    module H = {
      var m:(message * salt,htag * bool * signature) map

      fun init(): unit = { m = Map.empty; }

      fun o(c:bool,x:message * salt): htag = {
        var b:bool = true;
        var i:int = 0;
        var w:htag;
        var st:gtag;
        var z, u:signature;

        if (!in_dom x m)
        {
          while (i < kg2 && b)
          {
            u = $sample_plain I.pk;
            z = if c then (ystar * f pk u) pk else f pk u;
            b = (sub (to_bits z) 0 1 = ones 1);
            w = HTag.from_bits (sub (to_bits z) 1 k1);
            st = GTag.from_bits (sub (to_bits z) (k1 + 1) (kg));
            i = i + 1;
            if (!b)
            {
              m.[x] = (w,c,u);
              G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
            }
          }
        }
        else
        {
          if (!c /\ pi3_2 (proj I.H.m.[x])) m.[x] = (HTag.zeros,c,Signature.ones);
        }
        return pi3_1 (proj m.[x]);
      }
    }

    module Ha = {
      fun o(x:message * salt): htag = {
        var r:htag;
        r = H.o(true,x);
        return r;
      }
    }

    module IOracles = {
      var qs:message set

      fun sign(m:message): signature = {
        var r:salt;
        var w:htag;
        r = $sample_salt;
        w = H.o(false,(m,r));
        return pi3_3 (proj H.m.[(m,r)]);
      }
    }

    module A = A(G,Ha,IOracles)

    fun invert(pk:pkey,y:signature): signature = {
      var m:message;
      var s:signature;

      IOracles.qs = FSet.empty;
      I.pk = pk;
      ystar = y;
      (m,s) = A.forge(pk);

      return if !mem m IOracles.qs then s else Signature.zeros;
    }
  }.

  (** PROOF NOTE.
      The invariant below is insufficient. We need to know, at least:
        - forall m r w u,
            H.m.[m,r] = Some (w,false,u) =>
            w = sub (f pk u) 1 k1 /\
            G.m.[w] = Some (sub (f pk u) (k1 = 1) kg) ^ (r || zeros)
          (Note that this is currently not true when H is called directly,
           then by the signing oracle... This requires a bit of thought.)
        - forall m r w u,
            H.m.[m,r] = Some (w,true,u) =>
            w = sub ((f pk xstar) * (f pk u) [pk]) 1 k1 /\
            G.m.[w] = Some (sub ((f pk xstar) * (f pk u) [pk]) (k1 = 1) kg) ^ (r || zeros)
       There may also still be an upto bad step missing, that deals with the case where
       the adversary gets lucky and gets a valid signature out of fresh queries to H and G. *)
  local equiv G5_OW_H: H5.o ~ I.H.o:
    ={glob G, x, c} /\
    Hmap.m{1} = I.H.m{2} /\
    Hmem.pk{1} = I.pk{2} /\
    (f Hmem.pk Hmem.xstar){1} = I.ystar{2} ==>
    ={glob G, res} /\
    Hmap.m{1} = I.H.m{2} /\
    Hmem.pk{1} = I.pk{2} /\
    (f Hmem.pk Hmem.xstar){1} = I.ystar{2}.
  proof strict.
  fun; inline H5.o I.H.o; wp; sp; if=> //.
    wp; while (={glob G, i, b, c, x} /\
               Hmap.m{1} = I.H.m{2} /\
               Hmem.pk{1} = I.pk{2} /\
               (f Hmem.pk Hmem.xstar){1} = I.ystar{2})=> //.
      seq 6 6: (={glob G, u, w, st, i, b, c, x} /\
                Hmap.m{1} = I.H.m{2} /\
                Hmem.pk{1} = I.pk{2} /\
                (f Hmem.pk Hmem.xstar){1} = I.ystar{2} /\
                i{1} <= kg2).
        by wp; rnd; skip; smt.
        by if; try wp.
    by sp; if=> //; wp.
  qed.
end section.














































































(****** Old Material
(** Proof is up to bad with BAD = (b = true) in final memory *)
lemma equiv_G0_G1 (A <: CMA_2RO):
  equiv [G0(A(G,H)).main ~ G1(A(G,H1)).main: ={glob A} ==> !H1.bad{2} => ={res}].
admit. qed.
    
  module G0 
(** Inlining the oracles that do not need to change *)
module type PartialOracles = {
  fun init(): pkey
  fun sign(m:message): signature
  fun fresh(m:message): bool
}.


module SGen(H:Ht.Oracle): PartialOracles = {
  var pk:pkey
  var sk:skey

  var qs:message set

  fun init(): pkey = {
    G.init();
    H.init();
    qs = FSet.empty;
    (pk,sk) = $keypairs;
    Mem.init(pk,sk);
    return pk;
  }

  fun sign(m:message): signature = {
    var r:salt;
    var g:gtag;
    var rMask:salt;
    var maskedR:salt;
    var w:htag;
    var gamma:g2tag;
    var y:signature;

    qs = add m qs;
    r = $sample_salt;
    w  = H.o((m,r));
    g = G.o(w);
    rMask  = Salt.from_bits (sub (to_bits g) 0 k0);
    maskedR = rMask ^ r;
    gamma  = G2Tag.from_bits (sub (to_bits g) k0 kg2);
    y = Signature.from_bits (zeros 1 || (to_bits w) || (to_bits maskedR) || (to_bits gamma));
    return finv sk y;
  } 

  fun fresh(m:message): bool = {
    return !mem m qs;
  }
}.

module GGen(H:Ht.Oracle,O:PartialOracles,A:AdvCMA) = {
  module A = A(O)

  fun main(): bool = {
    var pk:pkey;
    var m:message;
    var s:signature;
    var y:signature;
    var w:htag;
    var w':htag;
    var g:gtag;
    var maskedR:salt;
    var gamma:g2tag;
    var gamma':g2tag;
    var rMask:salt;
    var r:salt;
    var forged, fresh:bool;

    pk = O.init();
    (m,s) = A.forge(pk);

    y = (f pk s);
    forged = (sub (to_bits y) 0 1 <> zeros 1);
    w = HTag.from_bits (sub (to_bits y) 1 k1);
    maskedR = Salt.from_bits (sub (to_bits y) (k1 + 1) k0);
    gamma = G2Tag.from_bits (sub (to_bits y) (k1 + k0 + 1) kg2);
    g = G.o(w);
    rMask  = Salt.from_bits (sub (to_bits g) 0 k0);
    r = rMask ^ maskedR;
    w'  = H.o((m,r));
    gamma'  = G2Tag.from_bits (sub (to_bits g) k0 kg2);
    forged =  w = w' /\ gamma = gamma' /\ !forged;

    fresh = O.fresh(m);
    return forged /\ fresh;
  }
}.

module G0 = GGen(H,SGen(H)).

(** H Oracle for G1 *)
op bool_nu: int -> bool distr.
axiom mu_bool_nu N p:
  2^(k - 1) <= N < 2^k =>
  mu (bool_nu N) p =
    ((N%r - (2^(k-1))%r) / N%r) * charfun p true + ((2^(k - 1))%r / N%r) * charfun p false.
lemma bool_nuL N:
  2^(k - 1) <= N < 2^k =>
  mu (bool_nu N) cpTrue = 1%r.
proof.
intros=> bounds; rewrite mu_bool_nu // /charfun /cpTrue /=.
cut ->: forall (a b:real), a / N%r + b / N%r = (a + b) / N%r by smt.
smt.
qed.

module H1: Ht.Oracle = {
  var bad:bool

  fun init(): unit = {
    H.init();
    bad = false;
  }

  fun o(x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    w = $sample_htag;
    if (!in_dom x H.m)
    {
      while (i < kg2 && b)
      {
        b = $bool_nu Mem.n;
        i = i + 1;
        if (!b)
          H.m.[x] = w;
      }
    }
    bad = bad \/ b;
    return proj H.m.[x];
  }
}.

module G1 = GGen(H1,SGen(H1)).

(** G2 *)
module H2: Ht.Oracle = {
  fun init(): unit = {
    H.init();
  }

  fun o(x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    if (!in_dom x H.m)
    {
      while (i < kg2 && b)
      {
        b = $bool_nu Mem.n;
        w = $sample_htag;
        i = i + 1;
        if (!b)
          H.m.[x] = w;
      }
    }
    return proj H.m.[x];
  }
}.

module G2 = GGen(H2,SGen(H2)).

equiv equiv_G1_G2 (A <: CMA_2RO):
  G1(A(G,H1)).main ~ G2(A(G,H2)).main: ={glob A} ==> ={res}.
admit. 
(** Proof goes by eager (rule for while in figure 3 in the ITP paper) *)
(* We may need to modify H2 so that it samples an initial (useless) value for w *)
(* Swapping statement is "if (b) w = $sample_htag;" *)
qed.

(** G3 *)
module H3: Ht.Oracle = {
  fun init(): unit = {
    H.init();
  }

  fun o (x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    var st:gtag;
    if (!in_dom x H.m)
    {
      while (i < kg2 && b)
      {
        b = $bool_nu Mem.n;
        w = $sample_htag;
        i = i + 1;
        if (!b)
        {
          H.m.[x] = w;
          st = G.o(w);
        }
      }
    }
    return proj H.m.[x];
  }
}.

module G3 = GGen(H3,SGen(H3)).

(** The proof is by two applications of the general eager-lazy transition for G:
      - first, we eagerly sample G,
      - then, we lazily sample it again (with some calls happening in H).        *)
equiv equiv_G2_G3 (A <: CMA_2RO):
  G2(A(G,H2)).main ~ G3(A(G,H3)).main: ={glob A} ==> ={res}.
admit. qed.

(** G4 *)
module H4: Ht.Oracle = {
  var bad:bool

  fun init(): unit = {
    H.init();
    bad = false;
  }

  fun o (x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    var st:gtag;
    if (!in_dom x H.m)
    {
      while (i < kg2 && b)
      {
        b = $bool_nu Mem.n;
        w = $sample_htag;
        st = $sample_gtag;
        i = i + 1;
        if (!b)
        {
          H.m.[x] = w;
          bad = bad \/ in_dom w G.m;
          G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
        }
      }
    }
    return proj H.m.[x];
  }
}.

module G4 = GGen(H4,SGen(H4)).

(** Proof is up to failure *)
equiv equiv_G3_G4 (A <: CMA_2RO):
  G3(A(G,H3)).main ~ G4(A(G,H4)).main: ={glob A} ==> !H4.bad{2} => ={res}.
admit. qed.

lemma G3_G4 (A <: CMA_2RO) &m:
  Pr[G3(A(G,H3)).main() @ &m: res] <= Pr[G4(A(G,H4)).main() @ &m: res] + Pr[G4(A(G,H4)).main() @ &m: H4.bad].
proof.
apply (Trans _ Pr[G4(A(G,H4)).main() @ &m: res \/ H4.bad]).
equiv_deno (equiv_G3_G4 A)=> //; smt.
rewrite Pr mu_or; smt.
qed.

(* We will need the invariant that `|dom G.m| <= qG *)
lemma Bad4 (A <: CMA_2RO) &m:
  Pr[G4(A(G,H4)).main() @ &m: H4.bad] <= (qS + qH)%r * (qG + qS + qH)%r/(2^k1)%r.
admit. qed.

(** Splitting the random oracle *)
module type SplitOracle = {
  fun init(): unit
  fun o(c:bool,x:message * salt):htag
}.

module Hs(H:SplitOracle): Ht.Oracle = {
  fun init(): unit = {
    H.init();
  }

  fun o(x:message * salt): htag = {
    var r:htag;
    r = H.o(false,x);
    return r;
  }
}.

module Ha(H:SplitOracle): Ht.Oracle = {
  fun init(): unit = {
    H.init();
  }

  fun o(x:message * salt): htag = {
    var r:htag;
    r = H.o(true,x);
    return r;
  }
}.

(** G5 *)
module H5: SplitOracle = {
  var bad:bool
  var m:(message * salt,htag * bool) map

  fun init(): unit = {
    bad = false;
    m = Map.empty;
  }

  fun o(c:bool,x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    var st:gtag;
    if (!in_dom x m)
    {
      while (i < kg2 && b)
      {
        b = $bool_nu Mem.n;
        w = $sample_htag;
        st = $sample_gtag;
        i = i + 1;
        if (!b)
        {
          m.[x] = (w,c);
          G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
        }
      }
    }
    else
    {
      if (!c /\ snd (proj m.[x]))
      {
        bad = true;
        m.[x] = (HTag.zeros,c);
      }
    }
    return fst (proj m.[x]);
  }
}.

module G5 = GGen(Hs(H5),SGen(Hs(H5))).




module H4': SplitOracle' = {
  var bad:bool

  fun init(): pkey * skey = {
    var ks: pkey * skey;
    ks = $keypairs;
    H.init();
    bad = false;
    return ks;
  }

  fun o (c:bool, x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    var st:gtag;
    if (!in_dom x H.m)
    {
      H.m.[x] = htag_dummy;
      while (i < kg2 && b)
      {
        b = $bool_nu Mem.n;
        w = $sample_htag;
        st = $sample_gtag;
        i = i + 1;
        if (!b)
        {
          H.m.[x] = w;
          bad = bad \/ in_dom w G.m;
          G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
        }
      }
    }
    return proj H.m.[x];
  }
}.

module H5': SplitOracle' = {
  var bad:bool
  var m:(message * salt,htag * bool) map

  fun init(): pkey * skey = {
    var ks : pkey * skey;
    ks = $keypairs;
    bad = false;
    m = Map.empty;
    return ks;
  }

  fun o(c:bool,x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    var st:gtag;
    if (!in_dom x m)
    {
      m.[x] = (htag_dummy , c);
      while (i < kg2 && b)
      {
        b = $bool_nu Mem.n;
        w = $sample_htag;
        st = $sample_gtag;
        i = i + 1;
        if (!b)
        {
          m.[x] = (w,c);
          G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
        }
      }
    }
    else
    {
      if (!c /\ snd (proj m.[x]))
      {
        bad = true;
        m.[x] = (HTag.zeros,c);
      }
    }
    return fst (proj m.[x]);
  }
}.


(* Remarque pas besoin de A avec les section *)

   

}.


  fun init(): pkey = {
    G.init();
    H.init();
    
    (pk,sk) = $keypairs;
    Mem.init(pk,sk);
    return pk;
  }

module GGen(H:Ht.Oracle,O:PartialOracles,A:AdvCMA) = {
  module A = A(O)

  fun main(): bool = {
    var pk:pkey;
    var m:message;
    var s:signature;
    var y:signature;
    var w:htag;
    var w':htag;
    var g:gtag;
    var maskedR:salt;
    var gamma:g2tag;
    var gamma':g2tag;
    var rMask:salt;
    var r:salt;
    var forged, fresh:bool;

    pk = O.init();
    (m,s) = A.forge(pk);

    y = (f pk s);
    forged = (sub (to_bits y) 0 1 <> zeros 1);
    w = HTag.from_bits (sub (to_bits y) 1 k1);
    maskedR = Salt.from_bits (sub (to_bits y) (k1 + 1) k0);
    gamma = G2Tag.from_bits (sub (to_bits y) (k1 + k0 + 1) kg2);
    g = G.o(w);
    rMask  = Salt.from_bits (sub (to_bits g) 0 k0);
    r = rMask ^ maskedR;
    w'  = H.o((m,r));
    gamma'  = G2Tag.from_bits (sub (to_bits g) k0 kg2);
    forged =  w = w' /\ gamma = gamma' /\ !forged;

    fresh = O.fresh(m);
    return forged /\ fresh;
  }
}.

pred eq_proj (m1: ('a,'b) map) (m2: ('a,'b*'c) map) = 
 forall a, in_dom a m1 = in_dom a m2 && 
     (in_dom a m1 => proj (m1.[a]) = fst (proj m2.[a])).

equiv equiv_G4_G5_o : H4.o ~ H5.o : 
          !H5.bad{2} /\ (eq_proj H.m{1} H5.m{2} /\ ={x,glob Gt.ROM.RO, glob SGen, glob Mem, glob G}) ==>
         !H5.bad{2} => (eq_proj H.m{1} H5.m{2} /\ ={res,glob Gt.ROM.RO, glob SGen, glob Mem, glob G}) .
proof.
  fun.
  seq 2 2 : (!H5.bad{2} /\ (eq_proj H.m{1} H5.m{2} /\ ={b,i,x,glob Gt.ROM.RO, glob SGen, glob Mem, glob G})).
     wp => //.
  if. 
    intros => &m1 &m2 [_ [X1 [ _ [ _ [ -> _ ]]]]].
    elim (X1 x{m2}) => -> //.
  while (eq_proj H.m{1} H5.m{2} /\ !H5.bad{2} /\ ={b,i,x,glob Gt.ROM.RO, glob SGen, glob Mem, glob G}).
    wp; do ? rnd;skip;progress => //.
    intros x';case (x' = x{2}); [intros => -> | intros Hdiff];smt.
  skip;progress => //.
    admit. (* We need to allways add a dummy value for x *)
  if{2};wp;skip;smt.
save.
   
equiv equiv_G4_G5 (A <: CMA_2RO{SGen,Gt.ROM.RO, H, H4,H5}):
  G4(A(G,H4)).main ~ G5(A(G,Ha(H5))).main: ={glob A} ==> !H5.bad{2} => ={res}.
proof.
  fun.
  seq 2 2 : (! H5.bad{2} => (eq_proj H.m{1} H5.m{2} /\ ={pk,m,s,glob Gt.ROM.RO,glob A, glob SGen,glob Mem, glob G})).
    call (_: H5.bad,  (eq_proj H.m{1} H5.m{2} /\ ={glob Gt.ROM.RO, glob SGen, glob Mem, glob G}), ={Mem.n}).
    admit.
    (* sign are the same *)
      fun.
      seq 3 3 : (! H5.bad{2} => eq_proj H.m{1} H5.m{2} /\ ={Gt.ROM.RO.m, glob SGen, glob Mem, glob G, r, w}).
        call (_: ! H5.bad{2} /\ (eq_proj H.m{1} H5.m{2} /\ ={x,glob Gt.ROM.RO, glob SGen, glob Mem, glob G}) ==>
               ! H5.bad{2} => (eq_proj H.m{1} H5.m{2} /\ ={res,glob Gt.ROM.RO, glob SGen, glob Mem, glob G})) .
          fun *. inline Hs(H5).o; wp.
          call equiv_G4_G5_o;wp;progress => //.
        rnd;wp;skip;progress => //;smt.
      case H5.bad{2}.
        conseq * ( _ : _ ==> true); first smt.
        wp;inline G.o;wp;rnd;wp;skip => //.
      conseq * ( _ : _ ==> ={y,glob Gt.ROM.RO, glob SGen, glob Mem, glob G} /\ eq_proj H.m{1} H5.m{2});
        first progress => //.
      eqobs_in (={glob Gt.ROM.RO, glob SGen, glob Mem, glob G}) (eq_proj H.m{1} H5.m{2}) : 
                (={y, glob Gt.ROM.RO, glob SGen, glob Mem, glob G});smt.
      admit.
      admit.
    (* H are the same *)
      fun *. inline Ha(H5).o;wp.
      call equiv_G4_G5_o;wp;skip;progress => //;smt.
      admit.
      admit.
    (* G are the same *)
      admit.
      admit.
      admit.
    (* Init *) 
    admit.
  inline SGen(H4).fresh SGen(Hs(H5)).fresh;wp.
  case H5.bad{2}.  
    call (_ : H5.bad{2} ==> H5.bad{2}).
      fun. inline H5.o.
      seq 2 4 : (i{2}=0 /\ i{1}=0 /\ H5.bad{2});[ wp;skip=> // | ].
      transitivity {1} { } (i{1} = 0 ==> true) (i{2} = 0 /\ H5.bad{2} ==> H5.bad{2}) => //.
        if{1}; [ | skip => //].
          while{1} true (kg2 - i{1}).
            intros &m z;wp; conseq * (_:_==> true);first smt.
            do ? (rnd;first smt).
            rnd. admit. (* we need more info on Mem.n, should allow to use mu_bool_nu *)
            skip => //.
        skip => //;smt.
      if{2}.
        wp;while{2} true (kg2 - i{2}).
          intros &m z;wp; conseq * (_:_==> true);first smt.
          do ? (rnd;first smt).
          rnd. admit. (* we need more info on Mem.n, should allow to use mu_bool_nu *)
          skip => //.
        skip => //;smt.
      wp;skip => //.
      conseq (_: _ ==> H5.bad{2}); first smt.
      wp;call (_: true ==> true).
       fun;wp;rnd=> //.
      wp => //.
  inline{2} Hs(H5).o;wp.
  call equiv_G4_G5_o;wp;progress => //.
  eqobs_in (={glob G}) (!H5.bad{2} /\ eq_proj H.m{1} H5.m{2}) : 
       (={m,g,w,gamma,forged, maskedR, glob Gt.ROM.RO, glob SGen, glob Mem, glob G}).
    progress => //.
  elim (H3 _) => //;progress.
  intros &m1 &m2 [H1 H2];elim (H1 _);progress => //.
qed.

lemma Bad5 (A <: CMA_2RO) &m:
  Pr[G5(A(G,Ha(H5))).main() @ &m: H5.bad] <= qS%r * (qS + qH)%r/(2^k0)%r.
admit. qed.

(** G6 *)
module H6: SplitOracle = {
  var bad:bool
  var m:(message * salt,htag * bool * signature) map

  fun init(): unit = {
    m = Map.empty;
  }

  fun o(c:bool,x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    var st:gtag;
    var z, u:signature;

    if (!in_dom x H.m)
    {
      while (i < kg2 && b)
      {
        b = $bool_nu Mem.n;
        w = $sample_htag;
        st = $sample_gtag;
        z = Signature.from_bits (if b then ones 1 else zeros 1 || to_bits w || to_bits st);
        u = if c then (Mem.xstar * finv Mem.sk  z) Mem.pk else finv Mem.sk z;
        i = i + 1;
        if (!b)
        {
          m.[x] = (w,c,u);
          G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
        }
      }
    }
    else
    {
      bad = true;
      if (!c) m.[x] = (HTag.zeros,c,Signature.zeros);
    }
    return proj H.m.[x];
  }
}.

module G6 = GGen(Hs(H6),SGen(Hs(H6))).

(** G7: No longer using sk to simulate the oracles *)
module H7: SplitOracle = {
  var bad:bool
  var m:(message * salt,htag * bool * signature) map

  fun init(): unit = {
    m = Map.empty;
  }

  fun o(c:bool,x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    var st:gtag;
    var z, u:signature;

    if (!in_dom x H.m)
    {
      while (i < kg2 && b)
      {
        u = $sample_plain;
        z = if c then (f Mem.pk Mem.xstar * f Mem.pk u) Mem.pk else f Mem.pk u;
        b = (sub (to_bits z) 0 1 = ones 1);
        w = HTag.from_bits (sub (to_bits z) 1 k1);
        st = GTag.from_bits (sub (to_bits z) (k1 + 1) (kg));
        i = i + 1;
        if (!b)
        {
          m.[x] = (w,c,u);
          G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
        }
      }
    }
    else
    {
      bad = true;
      if (!c) m.[x] = (HTag.zeros,c,Signature.zeros);
    }
    return (lambda abc, let (a,b,c) = abc in a) (proj m.[x]);
  }
}.

module G7 = GGen(Hs(H7),SGen(Hs(H7))).

(** Inverter *)
module I(A:CMA_2RO): Inverter = {
  var pk:pkey
  var n:int
  var ystar:signature

  module H = {
    var m:(message * salt,htag * bool * signature) map

    fun init(): unit = { }

    fun o(c:bool,x:message * salt): htag = {
      var b:bool = true;
      var i:int = 0;
      var w:htag;
      var st:gtag;
      var z, u:signature;

      if (!in_dom x H.m)
      {
        while (i < kg2 && b)
        {
          u = $sample_plain;
          z = if c then (ystar * f pk u) pk else f pk u;
          b = (sub (to_bits z) 0 1 = ones 1);
          w = HTag.from_bits (sub (to_bits z) 1 k1);
          st = GTag.from_bits (sub (to_bits z) (k1 + 1) (kg));
          i = i + 1;
          if (!b)
          {
            m.[x] = (w,c,u);
            G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
          }
        }
      }
      else
      {
        if (!c) m.[x] = (HTag.zeros,c,Signature.zeros);
      }
      return (lambda abc, let (a,b,c) = abc in a) (proj m.[x]);
    }
  }     

  module IOracles = {
    var qs:message set

    fun init(): unit = {
      qs = FSet.empty;
      H.m = Map.empty;
    }

    fun sign(m:message): signature = {
      var r:salt;
      var w:htag;
      r = $sample_salt;
      w = H.o(false,(m,r));
      return (lambda abc, let (a,b,c) = abc in c) (proj H.m.[(m,r)]);
    }

    fun fresh(m:message): bool = {
      return !mem m qs;
    }
  }

  module A = A(G,Ha(H),IOracles)

  fun inverter(pk:pkey,y:signature): signature = {
    var m:message;
    var s:signature;

    I.pk = pk;
    n = 3;
    ystar = y;
    (m,s) = A.forge(pk);

    return s;
  }
}.

equiv equiv_G7_OW (A<:CMA_2RO):
  G7(A(G,Ha(H7))).main ~ OW(I(A)).main: ={glob A} ==> ={res}.
proof strict.
  fun. inline{2} I(A).inverter;wp.
 I(A).A.forge.
admit. qed.

section.
declare module A:CMA_2RO {EF_CMA,Wrap,PSS,GGen,SGen,OW,G,Ha,Hs,H,H1,H2,H3,H4,H5,H6,H7}.
local module Ag = A(G).

local equiv equiv_PSS_G0:
  EF_CMA(Wrap(PSS(G,H)),Ag(H)).main ~ G0(Ag(H)).main: ={glob A} ==> ={res}.
proof strict.
fun.
inline Wrap(PSS(Gt.ROM.RO,Ht.ROM.RO)).verify
       PSS(Gt.ROM.RO,Ht.ROM.RO).verify
       PSS(Gt.ROM.RO,Ht.ROM.RO).g2
       Gt.ROM.RO.o
       PSS(Gt.ROM.RO,Ht.ROM.RO).g1.
swap{1} [21..25] -3;
eqobs_in;
rcondf{1} 21.
  intros=> &m; wp; rnd; wp; rnd; wp; call (_: true)=> //; call (_: true)=> //.
    skip; smt.
inline G.o.
wp; rnd{1}; wp;
rnd; wp;
call (_: ={glob Gt.ROM.RO, glob Ht.ROM.RO} /\
         Wrap.sk{1} = SGen.sk{2} /\
         Wrap.pk{1} = SGen.pk{2} /\
         Wrap.qs{1} = SGen.qs{2}).
  fun; inline PSS(Gt.ROM.RO,Ht.ROM.RO).sign
              PSS(Gt.ROM.RO,Ht.ROM.RO).g2 PSS(Gt.ROM.RO,Ht.ROM.RO).g1
              Gt.ROM.RO.o G.o; wp; rnd{1}; wp; rnd; wp;
       call (_: ={glob Ht.ROM.RO}); first by eqobs_in.
       rnd; wp; skip; progress=> //; smt.
  by fun; eqobs_in.
  by fun; eqobs_in.
inline Wrap(PSS(Gt.ROM.RO,Ht.ROM.RO)).init SGen(Ht.ROM.RO).init
       PSS(Gt.ROM.RO,Ht.ROM.RO).init PSS(Gt.ROM.RO,Ht.ROM.RO).keygen
       Mem.init.
wp; rnd{2}; wp; rnd; wp.
call (_: true ==> ={glob Ht.ROM.RO}); first by fun; eqobs_in.
call (_: true ==> ={glob Gt.ROM.RO}); first by fun; eqobs_in.
skip; progress=> //; smt.
qed.

(** Proof is up to bad with BAD = (b = true) in final memory *)
local equiv equiv_G0_G1_H:
  H.o ~ H1.o: ={x, glob H} /\ 2^(k - 1) <= Mem.n{2} < 2^k ==> !H1.bad{2} => ={res, glob H}.
fun; case (in_dom x ROM.RO.m){1}.
  rcondf{1} 2; [ | rcondf{2} 4 ]; first 2 by intros=> &m; rnd; wp.
  by wp; rnd; wp.

  rcondt{1} 2; [ | rcondt{2} 4 ]; first 2 by intros=> &m; rnd; wp.
  wp 2 4; while{2} (2^(k - 1) <= Mem.n < 2^k /\
                    eq_except H.m{1} H.m x /\
                    (!b => H.m.[x] = Some w)){2} (kg2 - i){2}.
    intros=> &m z; seq 1: (kg2 - i <= z /\ 2^(k - 1) <= Mem.n < 2^k /\ eq_except H.m{m} H.m x) 1%r 1%r 1%r 0%r.
      by rnd.
      by rnd (cpTrue); skip;
         intros=> &hr [[[[bounds nBad] [i_bound bad]] kg2_z] h]; rewrite bool_nuL //; smt.
      by wp; skip; progress=> //; smt.
      hoare; wp; skip; progress=> //; smt.
      by progress.
  swap{2} 3 -2; wp; rnd; skip; progress=> //; smt.
qed.

local equiv equiv_G0_G1:
  G0(Ag(H)).main ~ G1(Ag(H1)).main: ={glob A} ==> !H1.bad{2} => ={res}.
proof strict.
(* fun.
inline SGen(ROM.RO).fresh SGen(H1).fresh; wp.


fun; eqobs_in (={glob H}) true: (!H1.bad{1} => ={glob H}).
  fun; case (in_dom x ROM.RO.m){1}.
    rcondf{1} 2; first by intros=> &m; rnd.
    rcondf{2} 4; first by intros=> &m; rnd; wp.
    by wp; rnd; wp.

    rcondt{1} 2; first by intros=> &m; rnd.
    rcondt{2} 4; first by intros=> &m; rnd; wp.
    
*)
admit. qed.

lemma G0_G1 &m:
  Pr[G0(A(G,H)).main() @ &m: res] <= Pr[G1(A(G,H1)).main() @ &m: res] + Pr[G1(A(G,H1)).main() @ &m: H1.bad].
proof.
apply (Trans _ Pr[G1(A(G,H1)).main() @ &m: res \/ H1.bad] _).
equiv_deno (equiv_G0_G1)=> //; smt.
rewrite Pr mu_or; smt.
qed.

(** Maybe we need to fix the event to add a bound on the number of queries in the game *)
lemma Bad1 &m:
  Pr[G1(A(G,H1)).main() @ &m: H1.bad] <= (qS + qH)%r/(2^kg2)%r.
admit. qed.

end section.
*)