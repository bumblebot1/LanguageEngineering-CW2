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

write('Enter number: ');

read(x);

write('Factorial of '); write(x); write(' is ');

y := 1;

while !(x=1) do (

  y := y * x;

  x := x - 1

);

write(y);

writeln;

writeln;

{ OUT=append(_,[n!,_,_]) }


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
