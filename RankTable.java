/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import java.util.*;
//import coins.ssaforoldlir.*;

class Int {
    public int intValue;
    public Int (int val) {
	intValue = val;
    }
}

public class RankTable {
    private int rankSize;
    private int fBitLength;
    private Hashtable vecPool;
    private BitVector aVec;
    private Hashtable refCountPool;
    private int fShiftMax;


    public RankTable (int size) {
	rankSize = size;
	BitVector v = new BitVector(size);
	fBitLength = v.getBitLength();
	fShiftMax = fBitLength - 1;
	vecPool = new Hashtable();
	refCountPool = new Hashtable();
    }	

    public void insert(Object target, int rank) {
	BitVector vec = (BitVector)vecPool.get(target);
	Int refCount;

	if (vec == null) {
	    vec = new BitVector(rankSize);
	    refCount = new Int(1);
	    refCountPool.put(target+","+ rank, refCount);
	    vec.setBit(rank);
	    vecPool.put(target,vec);
	}
	else {
	    refCount = (Int)refCountPool.get(target+","+ rank);
	    if (refCount == null) {
		refCount = new Int(1);
		refCountPool.put(target+","+ rank, refCount);
		vec.setBit(rank);
	    }
	    else refCount.intValue++;
	}

    }
  
  public void insert(int rank) {
    Int refCount;

    if (aVec == null) {
      aVec = new BitVector(rankSize);
      refCount = new Int(1);
      refCountPool.put(""+ rank, refCount);
      aVec.setBit(rank);
    }
    else {
      refCount = (Int)refCountPool.get(""+ rank);
      if (refCount == null) {
	refCount = new Int(1);
	refCountPool.put(""+ rank, refCount);
	aVec.setBit(rank);
      }
      else refCount.intValue++;
    }
    
  }
    

    public void remove(Object target, int rank) {
	BitVector vec = (BitVector)vecPool.get(target);
	Int refCount;

	if (vec != null) {
	    refCount = (Int)refCountPool.get(target+","+ rank);
	    if (refCount != null) {
		if (refCount.intValue == 1) {
		    refCountPool.remove(target+","+rank);
		    vec.resetBit(rank);
		}
		else refCount.intValue--;
	    }
	}
    }

  public void remove(int rank) {
	Int refCount;

	if (aVec != null) {
	    refCount = (Int)refCountPool.get(""+ rank);
	    if (refCount != null) {
		if (refCount.intValue == 1) {
		    refCountPool.remove(""+rank);
		    aVec.resetBit(rank);
		}
		else refCount.intValue--;
	    }
	}
    }

    public boolean check (Object target, int lower, int upper) {
	int head, tail, hWord, hInx, tWord, tInx;

	head = lower+1;
	tail = upper-1;

	if (head > tail) return false;

	BitVector vec = (BitVector) vecPool.get(target);
	if (vec == null) return false;

	long[] fVectorWord = vec.getVectorWord();

	hWord = head / fBitLength;
	hInx  = head - hWord * fBitLength;
	tWord = tail / fBitLength;
	tInx  = tail - tWord * fBitLength;
	long hMask;
	if (hInx == 0)
	    hMask = ~(long)0x0;
	else
	    hMask = ~((~(long)0x0) << (fShiftMax-hInx+1));
	long tMask = (~(long)0x0) << (fShiftMax-tInx);
	if (hWord == tWord) 
	    if ((fVectorWord[hWord] & hMask & tMask) != 0) return true;
	    else return false;
	else if (tWord > hWord) {
	    if ((fVectorWord[hWord] & hMask) != 0) return true;
	    else if ((fVectorWord[tWord] & tMask) != 0) return true;
	    else if (tWord > hWord + 1) {
		for (int i = hWord + 1; i < tWord; i++)
		    if (fVectorWord[i] !=0) return true;
		return false;
	    }
	    else return false;
	}
	else return false;
    }

    public boolean check (int lower, int upper) {
	int head, tail, hWord, hInx, tWord, tInx;

	head = lower+1;
	tail = upper-1;

	if (head > tail) return false;

	if (aVec == null) return false;

	long[] fVectorWord = aVec.getVectorWord();

	hWord = head / fBitLength;
	hInx  = head - hWord * fBitLength;
	tWord = tail / fBitLength;
	tInx  = tail - tWord * fBitLength;
	long hMask;
	if (hInx == 0)
	    hMask = ~(long)0x0;
	else
	    hMask = ~((~(long)0x0) << (fShiftMax-hInx+1));
	long tMask = (~(long)0x0) << (fShiftMax-tInx);
	if (hWord == tWord) 
	    if ((fVectorWord[hWord] & hMask & tMask) != 0) return true;
	    else return false;
	else if (tWord > hWord) {
	    if ((fVectorWord[hWord] & hMask) != 0) return true;
	    else if ((fVectorWord[tWord] & tMask) != 0) return true;
	    else if (tWord > hWord + 1) {
		for (int i = hWord + 1; i < tWord; i++)
		    if (fVectorWord[i] !=0) return true;
		return false;
	    }
	    else return false;
	}
	else return false;
    }

}

