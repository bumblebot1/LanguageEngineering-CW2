{------------------------------------------------------------
 -- Language Engineering: COMS22201
 -- Assessed Coursework 2: CWK2
 -- Question 3: Axiomatic Semantics of While with read/write
 ------------------------------------------------------------
 -- This stub file gives two code fragments (from the test7.w
 -- source file used in CWK1) that you will need to annotate
 -- with tableau correctness proofs using the partial axiomatic
 -- semantics extended with axioms for read/write statements.
 --
 -- To answer this question, upload one file "cwk2.w" to the
 -- "CWK2" unit component in SAFE by midnight on 01/05/2016.
 --
 -- For further information see the brief at the following URL:
 -- https://www.cs.bris.ac.uk/Teaching/Resources/COMS22201/cwk2.pdf
 ------------------------------------------------------------}


{------------------------------------------------------------
 -- Part A)
 --
 -- provide a tableau-based partial correctness proof
 -- of the following program (for computing factorials)
 -- with respect to the given pre- and post-conditions
 -- by completing the annotation of the program with
 -- logical formulae enclosed within curly braces:
 ------------------------------------------------------------}

{ head(IN)=n }

write('Factorial calculator'); writeln;

{ head(IN)=n & OUT=append(_) }

write('Enter number: ');

{ head(IN)=n & OUT=append(_) }

read(x);

{ x=n & OUT=append(_) }

write('Factorial of '); write(x); write(' is ');

{ x=n & 1=1 & OUT=append(_) }

y := 1;

{ x=n & y=1 & OUT=append(_) }* Pre1
{ x>0 implies (x!*y=n! & OUT=append(_)) }

while !(x=1) do (
  { (x>0 implies (x!*y=n! & OUT=append(_))) & !(x=1) }** Pre2
  { x-1>0 implies ((x-1)!*x*y=n! & OUT=append(_)) }

  y := y * x;

  { x-1>0 implies (x-1)!*y=n! & OUT=append(_) }

  x := x - 1

  { x>0 implies (x!*y=n! & OUT=append(_)) }***Post2
  { x>0 implies (x!*y=n! & OUT=append(_)) }
);
{ (x>0 implies (x!*y=n! & OUT=append(_))) & !!(x=1) }****Post1
{ y=n! & OUT=append(_) }
write(y);

{ OUT=append(_,[n!]) }

writeln;

{ OUT=append(_,[n!,_]) }

writeln;

{ OUT=append(_,[n!,_,_]) }



PROOF OBLIGATIONS:
Pre1:
x=n & y=1 & OUT=append(_) |= (x>0 implies (x!*y=n! & OUT=append(_)))
(1)x=n           given
(2)y=1           given
(3)OUT=append(_) given
Moving on we need to distinguish between two cases (n>0 and n<=0)

case1: n<=0 then from (1) we get that x<=0 and we know that trivially
false implies true evaluates to true.

case2: n>0 then using (1) we find that x>0
(4)n!=n!                     by reflexivity of equality (factorial is well defined
                             due to assumption in case2)
(5)x!=n!                     from substituting (1) in (4)
(6)x!=1*x!                   definition of multiplication
(7)x!=y*x!                   substitute (2) in (6)
(8)n!=y*x!                   substitute (5) in (7)
(9)n!=y*x! & OUT=append(_)   trivial from (3) and (8)
Therefore in case2 the implication also holds true.
Due to the fact the the implication holds true in both cases we can conclude that
under any assignment for n the implication holds which means that
(x=n & y=1 & OUT=append(_)) |= (x>0 implies (x!*y=n! & OUT=append(_)))



Pre2:
((x>0 implies (x!*y=n! & OUT=append(_))) & !(x=1)) |= (x-1>0 implies ((x-1)!*x*y=n! & OUT=append(_)))
We only need to consider the cases x>0 or x<0
case1: x<0 means x-1<0 so the second implication trivially holds true (because false implies true yields true)

case2: x>0
(1) !(x=1)                                          given
(2) x>1                                             from (1) using the assumption in case2
(3) x-1>0                                           subtracting 1 from both sides in (2)
(4) x!*y=n!                                         given because we are in case2
(5) OUT=append(_)                                   given because we are in case2
(6) (x-1)!*x=x!                                     by the definition of factorial using the fact that x-1>0 from (3)
(7) (x-1)!*x*y=n!                                   substituting (6) in (4)
(8) (x-1)!*x*y=n! & OUT=append(_)                   from (7) and (5)
(9) (x-1>0 implies ((x-1)!*x*y=n! & OUT=append(_))  from (3) and (8) using the definition of implication
Therefore (x-1>0 implies ((x-1)!*x*y=n! & OUT=append(_))) is true in both cases which means
((x>0 implies (x!*y=n! & OUT=append(_))) & !(x=1)) |= (x-1>0 implies ((x-1)!*x*y=n! & OUT=append(_)))



Post2:
(x>0 implies (x!*y=n! & OUT=append(_))) |= (x>0 implies (x!*y=n! & OUT=append(_)))
This is trivially true due to the definition of logical entailment.



Post1:
((x>0 implies (x!*y=n! & OUT=append(_))) & !!(x=1)) |= (y=n! & OUT=append(_))
(1)!!(x=1)             given
(2)x=1                 by the definition of negation and (1)
(3)1>0                 by definition of >
(4)x>0                 substituting (2) into (3)
(5)x!*y=n!             by the definition of implication and using (4) in the implication
(6)OUT=append(_)       by the definition of implication and using (4) in the implication
(7)1!*y=n!             substituting (2) into (5)
(8)y=n!                by the definition of 1! and multiplication with 1
Therefore from (8) and (6) we can conclude that
((x>0 implies (x!*y=n! & OUT=append(_))) & !!(x=1)) |= (y=n! & OUT=append(_))
{------------------------------------------------------------
 -- Part B)
 --
 -- provide a tableau-based partial correctness proof
 -- of the following program (for computing exponents)
 -- with respect to suitable pre- and post-conditions:
 ------------------------------------------------------------}

write('Exponential calculator'); writeln;

write('Enter base: ');

read(base);

if 1 <= base then (

  write('Enter exponent: ');

  read(exponent);

  num := 1;

  count := exponent;

  while 1 <= count do (

    num := num * base;

    count := count - 1

  );

  write(base); write(' raised to the power of '); write(exponent); write(' is ');

  write(num)

) else (

  write('Invalid base '); write(base)

);

writeln
