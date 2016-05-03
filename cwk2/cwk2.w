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
false implies true evaluates to true so the implication holds true.

case2: n>0 then using (1) we find that x>0 so we need to prove the right hand side of the
implication holds.
(4)n!=n!                     by reflexivity of equality (factorial is well defined
                             due to assumption in case2 that n>0)
(5)x!=n!                     from substituting (1) in (4)
(6)x!=1*x!                   definition of multiplication
(7)x!=y*x!                   substitute (2) in (6)
(8)n!=y*x!                   substitute (5) in (7)
(9)n!=y*x! & OUT=append(_)   from (3) and (8)
Therefore in case2 the implication also holds true.
Due to the fact that the implication holds true in both cases we can conclude that
if (x=n & y=1 & OUT=append(_)) holds true then the implication holds true as well
which means that
(x=n & y=1 & OUT=append(_)) |= (x>0 implies (x!*y=n! & OUT=append(_)))



Pre2:
((x>0 implies (x!*y=n! & OUT=append(_))) & !(x=1)) |= (x-1>0 implies ((x-1)!*x*y=n! & OUT=append(_)))
(1) !(x=1)     given
We only need to consider the cases x>0 or x<=0
case1: x<=0 means x-1<0 so the second implication trivially holds true (because false implies true yields true)

case2: x>0
(2) x!*y=n!                                         given because (x>0 implies (x!*y=n! & OUT=append(_))) is true and we know x>0
(3) OUT=append(_)                                   same reason as 2
(4) x>1                                             from (1) using the assumption in case2
(5) x-1>0                                           subtracting 1 from both sides in (4)
(6) (x-1)!*x=x!                                     by the definition of factorial using the fact that x-1>0 from (5)
(7) (x-1)!*x*y=n!                                   substituting (6) in (2)
(8) (x-1)!*x*y=n! & OUT=append(_)                   from (7) and (3)
(9) (x-1>0 implies ((x-1)!*x*y=n! & OUT=append(_))  from (5) and (8) using the definition of implication
Therefore (x-1>0 implies ((x-1)!*x*y=n! & OUT=append(_))) is true in both cases which means
((x>0 implies (x!*y=n! & OUT=append(_))) & !(x=1)) |= (x-1>0 implies ((x-1)!*x*y=n! & OUT=append(_)))



Post2:
(x>0 implies (x!*y=n! & OUT=append(_))) |= (x>0 implies (x!*y=n! & OUT=append(_)))
This is trivially true due to the definition of logical entailment.



Post1:
((x>0 implies (x!*y=n! & OUT=append(_))) & !!(x=1)) |= (y=n! & OUT=append(_))
Let P=((x>0 implies (x!*y=n! & OUT=append(_))) & !!(x=1))
and Q=(y=n! & OUT=append(_))
(1)!!(x=1)             given
(2)x=1                 by the definition of negation and (1)
(3)1>0                 by definition of >
(4)x>0                 substituting (2) into (3)
(5)Because x>0 is true we must have that the second part of the implication is also true
in order for P to be true.
(6)x!*y=n!             from (5)
(7)OUT=append(_)       from (5)
(8)1!*y=n!             substituting (2) into (6)
(9)y=n!                by the definition of 1! and multiplication with 1
Therefore from (9) and (7) we can conclude that
((x>0 implies (x!*y=n! & OUT=append(_))) & !!(x=1)) |= (y=n! & OUT=append(_))
{------------------------------------------------------------
 -- Part B)
 --
 -- provide a tableau-based partial correctness proof
 -- of the following program (for computing exponents)
 -- with respect to suitable pre- and post-conditions:
 ------------------------------------------------------------}
{ head(IN)=a & head(tail(IN))=b & a>=1 & b>=1 }
write('Exponential calculator'); writeln;

{ head(IN)=a & head(tail(IN))=b & a>=1 & b>=1 & OUT=append(_) }

write('Enter base: ');

{ head(IN)=a & head(tail(IN))=b & a>=1 & b>=1 & OUT=append(_) }

read(base);

{ base=a & a>=1 & b>=1 & head(IN)=b & OUT=append(_) }

if 1 <= base then (
  { (1<=base) & base=a & a>=1 & b>=1 & head(IN)=b }

  write('Enter exponent: ');

  { (1<=base) & base=a & a>=1 & b>=1 & head(IN)=b & OUT=append(_) }

  read(exponent);

  { (1<=base) & base=a & a>=1 & b>=1 & exponent=b & OUT=append(_) }

  num := 1;

  { (1<=base) & base=a & a>=1 & b>=1 & exponent=b & num=1 & OUT=append(_) }

  count := exponent;

  { (1<=base) & base=a & a>=1 & b>=1 & exponent=b & num=1 & count=exponent & OUT=append(_) }***Pre1
  { num=base^(b-count) & count>=0 & base=a & a>=1 & b>=1 }

  while 1 <= count do (

    { num=base^(b-count) & count>=0 & base=a & a>=1 & b>=1 & count>=1}***Pre2
    { num*base=base^(b-(count-1)) & a>=1 & b>=1 & base=a & count-1>=0}

    num := num * base;

    { num=base^(b-(count-1)) & a>=1 & b>=1 & base=a & count-1>=0}

    count := count - 1

    { num=base^(b-count) & a>=1 & b>=1 & base=a & count>=0}***Post2
    { num=base^(b-count) & a>=1 & b>=1 & base=a & count>=0}
  );

  { num=base^(b-count) & a>=1 & b>=1 & base=a & count>=0 & !(count>=1) }***Post1
  { num=a^b }

  write(base); write(' raised to the power of '); write(exponent); write(' is ');

  { num=a^b & OUT=append(_) }

  write(num)

  { OUT=append(_,[a^b])}

) else (

  { !(1<=base) & base=a & a>=1 & b>=1 & head(IN)=b }***Pre3
  { base=a^b }

  write('Invalid base '); write(base)

  { OUT=append(_,[a^b])}***Post3
  { OUT=append(_,[a^b])}
);

{ OUT=append(_,[a^b]) }

writeln

{ OUT=append(_,[a^b,_]) }



PROOF OBLIGATIONS:
Pre1:
((1<=base) & base=a & a>=1 & b>=1 & exponent=b & num=1 & count=exponent & OUT=append(_)) |= (num=base^(b-count) & count>=0 & base=a & a>=1 & b>=1)
(1)  1<=base                              given
(2)  base=a                               given
(3)  a>=1                                 given
(4)  b>=1                                 given
(5)  exponent=b                           given
(6)  num=1                                given
(7)  count=exponent                       given
(8)  count=b                              substitute (7) in (5)
(9)  count>=1                             substitute (8) in (4)
(10) b-count=0                            from (8) by definition of -
(11) base^0 = 1                           by definition of ^(power in this case)
(12) base^(b-count)=1                     substituting (10) in (11)
(13) num = base^(b-count)                 substituting (6) in (12)
(14) 1>=0                                 by definition of >=
(15) count>=0                             using transitivity of >=; (9) and (11)
Therefore we can conclude that ((1<=base) & base=a & a>=1 & b>=1 & exponent=b & num=1 & count=exponent & OUT=append(_)) |= (num=base^(b-count) & count>=0 & base=a & a>=1 & b>=1)



Pre2:
(num=base^(b-count) & count>=0 & base=a & a>=1 & b>=1 & count>=1) |= (num*base=base^(b-(count-1)) & a>=1 & b>=1 & base=a & count-1>=0)
(1)   num=base^(b-count)                      given
(2)   count>=0                                given
(3)   base=a                                  given
(4)   a>=1                                    given
(5)   b>=1                                    given
(6)   count>=1                                given
(7)   count-1>=0                              by subtracting 1 from both sides in (6)
(8)   num*base=base*base^(b-count)            multiplying both sides by base in (1)
(9)   base*base^(b-count)=base^(b+1-count)    by definition of multiplication and power
(10)  base^(b+1-count)=base^(b-(count-1))     by associativity of + and -
(11)  base*base^(b-count)=base^(b-(count-1))  substituting (10) into (9)
(12)  num*base=base^(b-(count-1))             substituting (11) into (8)
Therefore we can conclude that (num=base^(b-count) & count>=0 & base=a & a>=1 & b>=1 & count>=1) |= (num*base=base^(b-(count-1)) & a>=1 & b>=1 & base=a & count-1>=0)



Post2:
(num=base^(b-count) & a>=1 & b>=1 & base=a & count>=0) |= (num=base^(b-count) & a>=1 & b>=1 & base=a & count>=0)
This is trivially true since the two statements are identical.



Post1:
(num=base^(b-count) & a>=1 & b>=1 & base=a & count>=0 & !(count>=1)) |= (num=a^b)
(1)   count>=0                given
(2)   !(count>=1)             given
(3)   count<1                 from (2)
(4)   count=0                 from (1) and (3)
(5)   base=a                  given
(6)   b-0=b                   by definition of subtraction with 0
(7)   b-count=b               substitute (4) into (6)
(8)   num=base^(b-count)      given
(9)   base^(b-count)=base^b   by raising base to the same power (7)
(10)  num=base^b              substitute (9) into (8)
(11)  base^b=a^b              raising both sides of (5) to the power of b
(12)  num=a^b                 by substituting (11) into (10)
Therefore we can conclude that (num=base^(b-count) & a>=1 & b>=1 & base=a & count>=0 & !(count>=1)) |= (num=a^b)



Pre3:
(!(1<=base) & base=a & a>=1 & b>=1 & head(IN)=b) |= (base=a^b)
(1) !(1<=base)   given
(2) base<1       from (1) by applying the negation to <=
(3) base=a       given
(4) a>=1         given
(5) base>=1      by transitivity from (3) and (4)
However we can now observe that (2) and (5) are mutually exclusive so when (2) is true
we must have (5) is false therefore the right side of the entailment is always false.
This means there exists no satisfying assignment for the left hand side for which the right hand side is false
(because no satisfying assignment for the left hand side exists). Therefore we can conclude that the entailment holds so:
(!(1<=base) & base=a & a>=1 & b>=1 & head(IN)=b) |= (base=a^b)



Post3:
OUT=append(_,[a^b]) |= OUT=append(_,[a^b])
Trivially true since both sides of the entailment are identical.
