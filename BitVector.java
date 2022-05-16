/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

/**
 * Bit vector for SSA optimization.
 * Original code is "coins.flow.BitVector.java".
 **/
public class BitVector{
  /** The word length of current bit vector **/
  private final int fLongWordLength;
  /** The bit length of current bit vector **/
  private final int fBitLength;
  /** The maximam number which can be shifted of current bit vector **/
  private final int fShiftMax;
  /** The bits are stored in it **/
  private long[] fVectorWord;

  /**
   * Constructor
   * @param elementsNum number of elements
   **/
  BitVector(int elementsNum){ 
    fBitLength=64;
    //fBitLength=32;
    fShiftMax=fBitLength-1;
    fLongWordLength=(elementsNum/fBitLength)+1;
    fVectorWord=new long[fLongWordLength];

    vectorReset();

    //System.out.println("++++++"+fLongWordLength+" "+fBitLength);
  }

  /**
   * Set specified bit.
   * @param pInx bit index number
   **/
  void setBit(int pInx){
    int lWord, lInx;
    lWord = pInx / fBitLength;
    lInx  = pInx - lWord * fBitLength;
    fVectorWord[lWord] = fVectorWord[lWord] | ((long)1 << (fShiftMax - lInx));

    //System.err.println(lWord+"   "+lInx); // debug, FUKUOKA Takeaki
  } // setBit

  /**
   * Reset specified bit.
   * @param pInx bit index number
   **/
  void resetBit( int pInx ){
    int  lWord, lInx;
    long lMask;
    lWord = pInx / fBitLength;
    lInx  = pInx - lWord * fBitLength;
    lMask = ~((long)1 << (fShiftMax - lInx));
    fVectorWord[lWord] = fVectorWord[lWord] & lMask;
  } // resetBit

  /**
   * Return specified bit.
   * @param pInx bit index number
   * @return The bit specified by the parameter.
   **/
  int getBit( int pInx ){
    int lWord, lInx, lBit;
    lWord = pInx / fBitLength;
    lInx  = pInx - lWord * fBitLength;

    //System.out.println(lWord+" "+lInx);

    lBit = (int)((fVectorWord[lWord] >> (fShiftMax - lInx)) & (long)1);

    //System.err.println(lWord+"   "+lInx); // debug, FUKUOKA Takeaki

    return lBit;
  } // getBit

  /**
   * Logical AND for bit vector.
   * @param pOperand2 operand bit vector.
   * @param pResult bit vector which is stored the result.
   **/
  void vectorAnd( BitVector pOperand2, BitVector pResult ){
    for (int i = 0; i < fLongWordLength; i++)
      ((BitVector)pResult).fVectorWord[i] = 
        ((BitVector)this).fVectorWord[i] & 
        ((BitVector)pOperand2).fVectorWord[i]; 
  } // vectorAnd

  /**
   * Logical OR for bit vector.
   * @param pOperand2 operand bit vector.
   * @param pResult bit vector which is stored the result.
   **/
  void vectorOr( BitVector pOperand2, BitVector pResult ) {
    for (int i = 0; i < fLongWordLength; i++)
      ((BitVector)pResult).fVectorWord[i] = 
        ((BitVector)this).fVectorWord[i] | 
        ((BitVector)pOperand2).fVectorWord[i]; 
  } // vectorOr

  /**
   * Logical XOR for bit vector.
   * @param pOperand2 operand bit vector.
   * @param pResult bit vector which is stored the result.
   **/
  void vectorXor( BitVector pOperand2, BitVector pResult ){
    for (int i = 0; i < fLongWordLength; i++)
      ((BitVector)pResult).fVectorWord[i] = 
        ((BitVector)this).fVectorWord[i] ^ 
        ((BitVector)pOperand2).fVectorWord[i]; 
  } // vectorXor

  /**
   * Logical NOT for bit vector.
   * @param pResult bit vector which is stored the result.
   **/
  void vectorNot( BitVector pResult ){
    for (int i = 0; i < fLongWordLength; i++)
      ((BitVector)pResult).fVectorWord[i] = 
        ~ ((BitVector)this).fVectorWord[i]; 
  } // vectorNot

  /**
   * SUB for bit vector.
   * @param pOperand2 operand bit vector.
   * @param pResult bit vector which is stored the result.
   **/
  void vectorSub( BitVector pOperand2, BitVector pResult ){ 
    for (int i = 0; i < fLongWordLength; i++)
      ((BitVector)pResult).fVectorWord[i] = 
        ((BitVector)this).fVectorWord[i] & 
        (~ ((BitVector)pOperand2).fVectorWord[i]); 
  } // vectorSub

  /**
   * Copy the current bit vector to another bit vector.
   * @param pResult bit vector which is stored the result.
   **/
  void vectorCopy( BitVector pResult ){
    for (int i = 0; i < fLongWordLength; i++)
      ((BitVector)pResult).fVectorWord[i] = 
        ((BitVector)this).fVectorWord[i]; 
  } // vectorCopy

  /**
   * Compare two bit vectors.
   * @param pOperand2 operand bit vector.
   * @return If two bit vectors are equal, return "true". otherwise "false".
   **/
  boolean vectorEqual( BitVector pOperand2 ){
    boolean lResult = false;
    int i = 0; 
    do {
      lResult = (((BitVector)this).fVectorWord[i] != 
                 ((BitVector)pOperand2).fVectorWord[i]); 
      i++;
    }while ((i < fLongWordLength)&&(lResult == false));
    return (! lResult);
  } // vectorEqual

  /**
   * Reset all bits in current bit vector.
   **/
  void vectorReset(){
    for (int i = 0; i < fLongWordLength; i++)
      ((BitVector)this).fVectorWord[i] = 0; 
  } // vectorReset

  /**
   * isEmpty:<br><br>
   * If all bits in current bit vector are unset, it mean "Empty".
   * @return If current bit vector is "Empty", return "true". 
   *         otherwise "false".
   **/
  boolean isEmpty(){
    for (int i = 0; i < fLongWordLength; i++)
      if (fVectorWord[i] != 0)
        return false;
    return true;
  } // isEmpty

  /**
   * Return the bit length of the current bit vector.
   * @return Bit length of current bit vector.
   **/
  int getBitLength(){
    return fBitLength;
  }

  /**
   * Return the word length of the current bit vector.
   * Word length is depend on machines.
   * @return Bit length of current bit vector.
   **/
  int getWordLength(){
    return fLongWordLength;
  }

  /**
   * Return the bits.
   * @return Array of long
   **/
  long[] getVectorWord(){
    return fVectorWord;
  }

  /**
   * Print out the current bit vector.
   **/
  private void print(){
    for(int j=0;j<32;j++){
      System.out.print(getBit(j)+" ");
    }
    System.out.println("");
  }
}
