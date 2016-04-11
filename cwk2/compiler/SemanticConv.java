// COMS22201: IR tree construction

import java.util.*;
import java.io.*;
import java.lang.reflect.Array;
import org.antlr.runtime.*;
import org.antlr.runtime.tree.*;

public class SemanticConv
{
// The code below is generated automatically from the ".tokens" file of the
// ANTLR syntax analysis, using the TokenConv program.
//
// CAMLE TOKENS BEGIN
  public static final String[] tokenNames = new String[] {
"NONE", "NONE", "NONE", "NONE", "AND", "ASSIGN", "CLOSEPAREN", "COMMENT", "DIV", "DO", "ELSE", "EQUALS", "FALSE", "IDENTIFIER", "IF", "INTNUM", "LOWERTHAN", "MINUS", "NOT", "OPENPAREN", "OR", "PLUS", "READ", "READR", "REALNUM", "SEMICOLON", "SKIP", "STRING", "SYMBOL", "THEN", "TIMES", "TRUE", "WHILE", "WRITE", "WRITELN", "WS"};
  public static final int AND=4;
  public static final int ASSIGN=5;
  public static final int CLOSEPAREN=6;
  public static final int COMMENT=7;
  public static final int DIV=8;
  public static final int DO=9;
  public static final int ELSE=10;
  public static final int EQUALS=11;
  public static final int FALSE=12;
  public static final int IDENTIFIER=13;
  public static final int IF=14;
  public static final int INTNUM=15;
  public static final int LOWERTHAN=16;
  public static final int MINUS=17;
  public static final int NOT=18;
  public static final int OPENPAREN=19;
  public static final int OR=20;
  public static final int PLUS=21;
  public static final int READ=22;
  public static final int READR=23;
  public static final int REALNUM=24;
  public static final int SEMICOLON=25;
  public static final int SKIP=26;
  public static final int STRING=27;
  public static final int SYMBOL=28;
  public static final int THEN=29;
  public static final int TIMES=30;
  public static final int TRUE=31;
  public static final int WHILE=32;
  public static final int WRITE=33;
  public static final int WRITELN=34;
  public static final int WS=35;
// CAMLE TOKENS END

  public static int freeLabel=0;
  static Map<String,String> table = Syn.table.getTable();

  public static void convert(CommonTree ast)
  {
    program(ast);
  }

  public static void program(CommonTree ast)
  {
    statements(ast);
  }

  public static void statements(CommonTree ast )
  {
    int i;
    Token t = ast.getToken();
    int tt = t.getType();
    if (tt == SEMICOLON) {
      CommonTree ast1 = (CommonTree)ast.getChild(0);
      CommonTree ast2 = (CommonTree)ast.getChild(1);
      System.out.print("Comp (");
      statements(ast1);
      System.out.print(")(");
      statements(ast2);
      System.out.print(")");
    }
    else {
      statement(ast);
    }
  }

  public static void statement(CommonTree ast)
  {
    CommonTree ast1, ast2, ast3;
    Token t = ast.getToken();
    int tt = t.getType();
    if (tt == WRITE) {
      ast1 = (CommonTree)ast.getChild(0);
      String type = arg(ast1);
    }
    else if (tt == WRITELN) {
      System.out.print("WriteLn");
    }
    else if(tt== ASSIGN){
      ast1 = (CommonTree)ast.getChild(0);
      ast2 = (CommonTree)ast.getChild(1);
      Token t1=ast1.getToken();//IDENTIFIER name of the variable
      Token t2=ast2.getToken();//Value of the variable
      int tt1=t1.getType();
      int tt2=t2.getType();

      if(tt1==IDENTIFIER){
        System.out.print("Ass \""+t1.getText()+"\" (");
        expression(ast2);
        System.out.print(")");
      }
      else{
        error(tt);
      }
    }
    else if(tt == READ){
      ast1=(CommonTree)ast.getChild(0);
      Token t1=ast1.getToken();//IDENTIFIER name of the variable
      System.out.print("Read \""+t1.getText()+"\"");
    }
    else if(tt == IF){
      ast1=(CommonTree)ast.getChild(0);
      ast2=(CommonTree)ast.getChild(1);
      ast3=(CommonTree)ast.getChild(2);
      System.out.print("If (");
      expression(ast1);
      System.out.print(")(");
      statement(ast2);
      System.out.print(")(");
      statement(ast3);
      System.out.print(")");
    }
    else if(tt == SKIP){
      System.out.print("Skip");
    }
    else if(tt == SEMICOLON){
      statements(ast);
    }
    else if(tt == WHILE){
      ast1=(CommonTree)ast.getChild(0);
      ast2=(CommonTree)ast.getChild(1);
      System.out.print("While (");
      expression(ast1);
      System.out.print(")(");
      statement(ast2);
      System.out.print(")");
    }
    else {
      error(tt);
    }
  }

  public static String arg(CommonTree ast)
  {
    Token t = ast.getToken();
    int tt = t.getType();
    if (tt == STRING) {
      String tx = t.getText();
      System.out.print("WriteS \""+tx+"\"");
      return "string";
    }
    else if(tt == TRUE){
      System.out.print("WriteB ");
      expression(ast);
      return "boolean";
    }
    else if(tt == FALSE){
      System.out.print("WriteB ");
      expression(ast);
      return "boolean";
    }
    else if(tt == NOT){
      System.out.print("WriteB ");
      expression(ast);
      return "boolean";
    }
    else if(tt == AND){
      System.out.print("WriteB ");
      expression(ast);
      return "boolean";
    }
    else if(tt == EQUALS){
      System.out.print("WriteB ");
      expression(ast);
      return "boolean";
    }
    else if(tt == LOWERTHAN){
      System.out.print("WriteB ");
      expression(ast);
      return "boolean";
    }
    else {
      System.out.print("WriteA (");
      expression(ast);
      System.out.print(")");
      return "int";
    }
  }

  public static void expression(CommonTree ast)
  {
    CommonTree ast1;
    CommonTree ast2;
    Token t = ast.getToken();
    int tt = t.getType();
    if (tt == INTNUM) {
      System.out.print("N ");
      constant(ast);
    }
    else if(tt == IDENTIFIER){
      String var = t.getText();
      System.out.print("V \""+var+"\"");
    }
    else if(tt==PLUS){
      ast1=(CommonTree) ast.getChild(0);
      ast2=(CommonTree) ast.getChild(1);
      System.out.print("Add (");
      expression(ast1);
      System.out.print(") (");
      expression(ast2);
      System.out.print(")");
    }
    else if(tt==MINUS){
      ast1=(CommonTree) ast.getChild(0);
      ast2=(CommonTree) ast.getChild(1);
      System.out.print("Sub (");
      expression(ast1);
      System.out.print(") (");
      expression(ast2);
      System.out.print(")");
    }
    else if(tt==TIMES){
      ast1=(CommonTree) ast.getChild(0);
      ast2=(CommonTree) ast.getChild(1);
      System.out.print("Mult (");
      expression(ast1);
      System.out.print(") (");
      expression(ast2);
      System.out.print(")");
    }

    else if(tt==EQUALS){
      ast1=(CommonTree) ast.getChild(0);
      ast2=(CommonTree) ast.getChild(1);
      System.out.print("Eq (");
      expression(ast1);
      System.out.print(") (");
      expression(ast2);
      System.out.print(")");
    }
    else if(tt==LOWERTHAN){
      ast1=(CommonTree) ast.getChild(0);
      ast2=(CommonTree) ast.getChild(1);
      System.out.print("Le (");
      expression(ast1);
      System.out.print(") (");
      expression(ast2);
      System.out.print(")");

    }
    else if(tt==NOT){
      ast1=(CommonTree) ast.getChild(0);
      System.out.print("Neg (");
      expression(ast1);
      System.out.print(")");
    }
    else if(tt==AND){
      ast1=(CommonTree) ast.getChild(0);
      ast2=(CommonTree) ast.getChild(1);
      System.out.print("And (");
      expression(ast1);
      System.out.print(") (");
      expression(ast2);
      System.out.print(")");
    }
    else if(tt==TRUE){
      System.out.print("TRUE");
    }
    else if(tt==FALSE){
      System.out.print("FALSE");
    }
    else{
        error(tt);
    }
  }



  public static void constant(CommonTree ast)
  {
    Token t = ast.getToken();
    int tt = t.getType();
    if (tt == INTNUM) {
      String tx = t.getText();
      System.out.print(tx);
    }
    else {

      error(tt);
    }
  }

  private static void error(int tt)
  {
    System.out.println("Hask error: "+tokenNames[tt]);
    System.exit(1);
  }
}
