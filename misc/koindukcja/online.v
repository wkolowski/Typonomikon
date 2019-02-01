Require Import Arith.

CoInductive stream (A : Type) : Type :=
    | snil : stream A
    | scons : A -> stream A -> stream A.

Arguments snil [A].
Arguments scons [A] _ _.

CoFixpoint ins (n : nat) (s : stream nat) : stream nat :=
match s with
    | snil => scons n snil
    | scons m s' =>
        if n <=? m
        then scons n (scons m s')
        else scons m (ins n s')
end.

CoFixpoint ss (s : stream nat) : stream nat :=
match s with
    | snil => snil
    | scons h t => match ss t with
        | snil => scons h snil
        | scons h' t' => ins h (scons h' t')
    end
end.