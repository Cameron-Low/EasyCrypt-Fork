require import AllCore Distr.

type t, u.

module BiSample = {
  proc sample(dt : t distr, du : u distr) = {
    var t, u;

    t <$ dt;
    u <$ du;
    return (t, u);
  }
}.

module Prod = {
  proc sample(dt : t distr, du : u distr) = {
    var tu;

    tu <$ dt `*` du;
    return tu;
  }
}.

equiv eq: BiSample.sample ~ Prod.sample: ={arg} ==> ={res}.
proof. admitted.

equiv eq': BiSample.sample ~ Prod.sample: ={arg} ==> ={res}.
proof.
proc.
transitivity {1} { (t,u) <@ BiSample.sample(dt,du); }
  (={dt,du} ==> ={t,u})
  (={dt,du} ==> (t,u){1} = tu{2});
    [4:transitivity {2} { tu <@ Prod.sample(dt,du); }
    (={dt,du} ==> (t,u){1} = tu{2})
    (={dt,du} ==> ={tu})];
  [ 3,7:inline *; try (auto; done)
  |   6:call eq]; trivial.
+ move=> &1 &2 H; exists dt{1} du{1}; move: H => //.
+ move=> &1 &2 H; exists dt{1} du{1}; move: H => //.
by auto=> /> [].
qed.

pred P. pred Q.
axiom PQ: P => Q.

require Distr.
equiv eq2: BiSample.sample ~ Prod.sample: arg{2} = arg{1} /\ P ==> res{2} = res{1} /\ Q.
proof.
proc.
rewrite equiv [{1} 1 eq (dt, du) (t,u) (dt, du) tu].
+ move=> &1 &2 H; exists dt{1} du{1}; move: H => //.
+ move=> &1 &2 H; exists dt{1} du{1}; move: H => //.
by auto=> /> /PQ -> [].
qed.

equiv eq3: Prod.sample ~ BiSample.sample: arg{2} = arg{1} /\ P ==> res{2} = res{1} /\ Q.
proof.
proc.
rewrite equiv [{2} 1 eq (dt, du) (t,u) (dt, du) tu]=> //.
+ move=> &1 &2 H; exists dt{2} du{2}; move: H => //.
+ move=> &1 &2 H; exists dt{2} du{2}; move: H => //.
by auto=> /> /PQ -> [].
qed.

op defaultT : t.
op defaultU : u.

module C = {
  proc foo(switch : bool, dt : t distr, du : u distr) : t * u = {
    var t, u;

    t <$ dt;
    u <$ du;
    if (switch) {
      t <- defaultT;
      u <- defaultU;
    }
    return (t, u);
  }
}.

op default : t * u.

module D = {
  proc bar(switch : bool, dt : t distr, du : u distr) : t * u = {
    var tu;
    tu <$ dt `*` du;
    if (switch) {
      tu <- default;
    }
    return tu;
  }
}.

equiv switch: C.foo ~ D.bar : switch{1} = false /\ switch{2} = false /\ ={dt, du} ==> ={res}.
proof.
proc.
transitivity {1} { (t,u) <@ BiSample.sample(dt,du); }
(={dt,du} /\ (switch{1} = false /\ switch{2} = false) ==> ={t,u})
(={dt,du} /\ (switch{1} = false /\ switch{2} = false) ==> (t,u){1} = tu{2});
[4:transitivity {2} { tu <@ Prod.sample(dt,du); }
  (={dt,du} /\ (switch{1} = false /\ switch{2} = false) ==> (t,u){1} = tu{2})
  (={dt,du} /\ switch{2} = false ==> ={tu})];
[ 3,7:inline *; try (auto; done)
|   6:call eq]; trivial.
+ move=> &1 &2 H; exists dt{1} du{1} switch{1}; move: H => //.
+ move=> &1 &2 H; exists dt{1} du{1} switch{1}; move: H => //.
by auto=> /> [].
qed.

equiv switch': C.foo ~ D.bar : switch{1} = false /\ switch{2} = false /\ ={dt, du} ==> ={res}.
proof.
proc.
rewrite equiv [{1} 1 eq (dt, du) (t, u) (dt, du) tu].
+ move=> &1 &2 H; exists dt{1} du{1} switch{1}; move: H => //.
+ move=> &1 &2 H; exists dt{1} du{1} switch{1}; move: H => //.
by auto=> /> [].
qed.
