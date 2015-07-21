import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.sql.Date;
import java.text.SimpleDateFormat;
import java.util.BitSet;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BrokenBarrierException;
import java.util.concurrent.CyclicBarrier;
import java.util.concurrent.RejectedExecutionException;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

public final class BealsConjectureExecutor 
{    
    private static final String LOG_FILENAME = "C:\\Users\\John McGonagle\\Desktop\\BealsConjecture\\CalcLog.txt";
    private static final String BIG_PRIMES_FILENAME = "C:\\Users\\John McGonagle\\Desktop\\BealsConjecture\\BigPrimes.txt";
    
    private static final int MAX_NUM = 1000;
    private static final int MIN_EXP = 3;
    private static final int MAX_EXP = 1000;
    private static final int POOL_SIZE = 100;
    private static final int STATUS_WAIT = 10000;
    
    private static BitSet[] coprimesList;
    private static int[] bigPrimesList;
    
    private static BufferedOutputStream calculationLogWriter;
    private static BufferedReader bigPrimesReader;
    private static CyclicBarrier barrier;
    
    private static BealsConjectureExecutor BCE;
    private static int threadCount;
    private static int tupleCount;
    private static boolean progressNotDisplayed;
 
    private static ThreadPoolExecutor threadPoolExec;
    private static ArrayBlockingQueue<Runnable> queue;
    
    private static final Object printLock = new Object();
    private static final Object threadCountLock = new Object();
    private static final Object syncArrayListLock = new Object();
    
    public BealsConjectureExecutor()
    {
        queue = new ArrayBlockingQueue<Runnable>(POOL_SIZE);
        threadPoolExec = new ThreadPoolExecutor(POOL_SIZE, POOL_SIZE,
                		 					    10, TimeUnit.SECONDS, queue);
        threadPoolExec.setRejectedExecutionHandler(new ThreadPoolExecutor.CallerRunsPolicy());
        
        bigPrimesList = new int[15240];
        coprimesList = new BitSet[MAX_NUM + 1];
        
    	barrier = new CyclicBarrier(7);
    	
    	progressNotDisplayed = false;
        tupleCount = 0;
    }
 
    private final void runTask(Runnable task)
    {
    	try 
    	{
    		threadPoolExec.execute(task);
    	}
    	catch (RejectedExecutionException rej) 
    	{
    		///*
    		synchronized(printLock) 
    		{
    			System.out.println("\nTask Rejected: " + task.toString() + "\n");
    		}
    		//*/
    		
			try 
    		{
				Thread.sleep(15000);
			} 
    		catch (InterruptedException e) 
    		{
    			synchronized(printLock) 
    			{
    				System.out.println("\nCurrent thread sleep interrupted\n");
    			}
			}
			
    		synchronized (threadCountLock) 
    		{
    			threadCount--;
    		}
    		
    		runHandler(task);
    	}
    }
    
    private final void runHandler(Runnable task) 
    {
    	synchronized(threadCountLock)
    	{
    		threadCount++;
    		runTask(task);
    		threadCount--;
    	}
    }
 
    private final void shutdown()
    {
        threadPoolExec.shutdown();
    }
    
    private static final void Trunk2TuplePrecursor(final int branch1, final int branch2) 
    {
    	BCE.runHandler(new Runnable()
        {
	    	public void run()
	        {                	
	        	generateCoprime2Tuples(branch1, branch2);
	        	
	        	try {
					barrier.await();
	        	}
				catch (InterruptedException e) 
				{
					synchronized(printLock) 
					{
						System.out.println("Thread waiting at barrier interrupted");
					}
				}
				catch (BrokenBarrierException e) 
				{
					synchronized(printLock) 
					{
						System.out.println("Barrier was broken unexpectedly");
					}
				}
	        }
        });
    }

    //switches a, b if a > b
    private static final boolean coprimeTwoTest(final int a, final int b) 
    {
    	if ((a == 0)) {
    		if (b == 1) {
    			return true;
    		}
    		else {
    			return false;
    		}
    	}
    	else if (b == 0) {
    		if (a == 1) {
    			return true;
    		}
    		else {
    			return false;
    		}
    	}
    	else {
    		return coprimeTwoTest((b - (a * (b / a))), a);
    	}
    }
    
    private static final boolean coprimeThreeTest(final int a, final int b, final int c) 
    {
    	return (coprimeTwoTest(a, b) && coprimeTwoTest(b, c) && coprimeTwoTest(c, a));
    }
    
    private static final void generateCoprime2Tuples(final int m, final int n) 
    {
    	if ((m <= MAX_NUM) && (n <= MAX_NUM))
    	{
    		/*
    		synchronized(syncArrayListLock) {
		        if (coprimesList[m] == null)
		        {
		        	coprimesList[m] = (new BitSet(MAX_NUM + 1));
		        }
		        
		        if (coprimesList[n] == null)
		        {
		        	coprimesList[n] = (new BitSet(MAX_NUM + 1));
		        }
    		}
	        
	        if (m > n) {
	        	coprimesList[n].set(m);
	        }
	        else {
	        	coprimesList[m].set(n);
	        }
	        */
    		
    		int min = Math.min(m, n);
    		int max = Math.max(m, n);
    		
	        testPythagTriple(Math.pow(max,  2) - Math.pow(min,  2), 2 * max * min, Math.pow(min,  2) + Math.pow(max,  2));
    		
	    	generateCoprime2Tuples(2 * m - n, m);
	    	generateCoprime2Tuples(2 * m + n, m);
	    	generateCoprime2Tuples(2 * n + m, n);
    	}
    }
    
    
    private static final void generatePairwiseCoprime3Tuples() 
    {
    	BitSet firstNumSet;
    	BitSet pairwiseCoprimeSet;
    	
    	int i, j, k;
    	
    	for (i = 2; i  <= MAX_NUM; i++) 
    	{
    		firstNumSet = coprimesList[i];
    		
    		if ((i % 100) == 0) 
    		{
	    		synchronized(printLock) 
	    		{
	    			System.out.println("Tuple base: " + i);
	    		}
    		}

    		for (j = i + 1; j <= MAX_NUM; j++)
    		{
    			if(firstNumSet.get(j)) 
    			{
    				pairwiseCoprimeSet = ((BitSet) coprimesList[j].clone());
    				pairwiseCoprimeSet.and(firstNumSet);
    				
    				for (k = j + 1; k <= MAX_NUM; k++) 
    				{	
    					if (pairwiseCoprimeSet.get(k)) 
    					{
    						testOrdered3Tuples(i, j, k);
    						/*
	    					//synchronized(printLock) 
	    					{
	    						System.out.println("Coprime 3-Tuple Found: " + i + "," + j + "," + k);
	    					
		    					try {
		    		    			calculationLog.write((new String("\nCoprime 3-Tuple Found: " + i + "," + j + "," + k)).getBytes());
		    		    			
		    		    			calculationLog.flush();
		    		    		}
		    		        	catch (IOException e) 
		    		    		{
		    		    			
		    		    			System.out.println("\nNot able to write to file at " + FILENAME + "\n");
		    		    		}
		    		    	}
	    		    		*/
    					}
    				}
    			}
			}
    	}
    }

    private static final void testOrdered3Tuples(final int a, final int b, final int c)
    {    	
    	///*
    	BCE.runHandler(new Runnable()
        {
            public void run()
            {                	
            	testCoprime3Tuple(a, b, c, 0);
            }
        });
    	
    	BCE.runHandler(new Runnable()
        {
            public void run()
            {
            	testCoprime3Tuple(b, a, c, 1);
            }
        });
    	
    	BCE.runHandler(new Runnable()
        {
            public void run()
            {
            	testCoprime3Tuple(c, a, b, 0);
            }
        });
    	
    	BCE.runHandler(new Runnable()
        {
            public void run()
            {
            	testCoprime3Tuple(a, c, b, 1);
            }
        });
    	
    	BCE.runHandler(new Runnable()
        {
            public void run()
            {                	
            	testCoprime3Tuple(b, c, a, 0);
            }
        });
    	
    	BCE.runHandler(new Runnable()
        {
            public void run()
            {
            	testCoprime3Tuple(c, b, a, 1);
            }
        });
        //*/
    	
    	tupleCount++;

    	if (progressNotDisplayed && ((tupleCount % STATUS_WAIT) == 0))
    	{
    		synchronized(printLock) 
    		{
    			if (progressNotDisplayed) 
    			{
    				progressNotDisplayed = false;
    				
	    			System.out.println("Progress: " + tupleCount + " 3-Tuples Examined");
	    			
	    			try {
	        			calculationLogWriter.write((new String("\n############################################" +
	        											 "Progress: " + tupleCount + " Coprime 3-Tuples Examined" +
	        											 "\n############################################\n\n")).getBytes());
	        			
	        			calculationLogWriter.flush();
	        		}
	            	catch (IOException e) 
	        		{
	        			System.out.println("\nNot able to write to file at " + LOG_FILENAME + "\n");
	        		}
    			}
    		}
    	}
    	else if (!progressNotDisplayed && ((tupleCount % 95) == 0))
    	{
    		progressNotDisplayed = true;
    	}
    }
    
    private static final void testCoprime3Tuple(final int A, final int B, final int C, final int abSeen)
    {
    	/*
    	synchronized(printLock) {
    		System.out.println("Testing Tuple: " + "(" + A + "," + B + "," + C + ")");
    	}
    	*/
    	
    	int X, Y, Z, P, prime;
    	boolean foundSomething = true;
        
    	final int numCoprimeModuli = ((int) (MAX_EXP * Math.log(Math.max(Math.max(A, B), C)))) + 1;
    	
        for (X = MIN_EXP; X <= MAX_EXP; X++)
        {
            for (Y = (X + abSeen); Y <= MAX_EXP; Y++)
            {
                    for (Z = MIN_EXP; Z <= MAX_EXP; Z++)
                    {
                    	for (P = 0; P < numCoprimeModuli; P++)
                    	{
                    		prime = bigPrimesList[P];
                    		
                    		if ((((modularExp((A % prime), (X % (prime - 1)), prime)) + 
                    			  (modularExp((B % prime), (Y % (prime - 1)), prime))) % prime) != (modularExp((C % prime), (Z % (prime - 1)), prime)))
                    		{
                    			foundSomething = false;
                    			break;
                    		}
                    	}
                    	
                    	if (foundSomething) {
	                		//Toolkit.getDefaultToolkit().beep();
	                    	
	                    	synchronized(printLock) 
	                    	{
	                            System.out.println("\n##################" +
	                            				   "\nPossible Solution: " +
	                                               A + "^" + X + " + " +
	                                               B + "^" + Y + " = " +
	                                               C + "^" + Z +
	                                    		   "\n##################\n");
	                            
	                            try 
	                            {
		                			calculationLogWriter.write((new String("\n##################" +
		                											 "\nPossible Solution: " +
		                											 A + "^" + X + " + " +
		                											 B + "^" + Y + " = " +
		                											 C + "^" + Z +
		                        		   							 "\n##################\n").getBytes()));
		                			
		                			calculationLogWriter.flush();
	                    		}
	                        	catch (IOException e) 
	                    		{
	                    			synchronized(printLock) 
	                    			{
	                    				System.out.println("\nNot able to write to file at " + LOG_FILENAME + "\n");
	                    			}
	                    		}
	                    	}
	                    }
                    	
                    	foundSomething = true;
                    }
                }
            }
        }
    
    

    private static final int modularExp(int base, int exponent, final int modulus) 
    {
        int result = 1;
        //int origBase = base;
        //int origExp = exponent;
        
        if (base < 2) {
        	return base;
        }
        while (exponent > 0)
        {
            if ((exponent & 1) == 1)
            {
                result = (result * base) % modulus;
            }

            exponent = exponent >> 1;
            base = (base * base) % modulus;
        }

        //System.out.println(origBase + "^" + origExp + " = " +
        //                   result + " (mod " + modulus + ")");

        return result;
    }
    
    private static void getBigPrimesFromFile() 
    {
        int nextRow = 0;
        String fileLine;
        
        FileInputStream fstream = null;
        
    	try 
    	{
            fstream = new FileInputStream(BIG_PRIMES_FILENAME);
		}
    	catch (FileNotFoundException e1) 
    	{
			System.out.println("\nFile not found at: " + BIG_PRIMES_FILENAME + "\n");
		}

        DataInputStream in = new DataInputStream(fstream);
		bigPrimesReader = new BufferedReader(new InputStreamReader(in));
		        
        try {
			while ((fileLine = bigPrimesReader.readLine()) != null) 
			{
			    nextRow = processPrimeFileString(fileLine, nextRow);
			}
		} 
        catch (IOException e)
		{
			System.out.println("Problems reading file at: " + BIG_PRIMES_FILENAME + "\n");
		}
        
        System.out.println("All primes read from file!\n");
    }
    
    private static int processPrimeFileString(String primeRow, int nextRow) {
    	String[] primeStrings = primeRow.trim().split(",");
		
		for (int i = 0; i < primeStrings.length; i++) 
		{
			bigPrimesList[nextRow++] = Integer.valueOf(primeStrings[i].trim());

			//System.out.print(bigPrimesList[nextRow - 1] + ",");
		}
		
		return nextRow;
	}

	public static void main(String[] args)
    {    
		System.out.print(coprimeTwoTest(30, 3));
		/*
    	BCE = new BealsConjectureExecutor();
    	
    	try {
			calculationLogWriter = new BufferedOutputStream(new FileOutputStream(LOG_FILENAME, true));
		} catch (FileNotFoundException e1) {
			synchronized(printLock) 
			{
				System.out.println("\nWARNING: File at " + LOG_FILENAME +
								   "\n not found.  This session will not be recorded.\n");
			}
		}
    	
    	Date today = new Date(System.currentTimeMillis());
    	SimpleDateFormat formatter = new SimpleDateFormat("EEE, d MMM yyyy hh:mm:ss a");
    	String timeString = formatter.format(today);
    	
    	System.out.println("\n\n#######################################################"  +
						   "\nCalculations started on " + timeString + "\n\n");
    	
    	try 
    	{
			calculationLogWriter.write((new String("\n\n#######################################################"  +
								 			 "\nCalculations started on " + timeString + "\n\n")).getBytes());
			
			calculationLogWriter.flush();
		} 
    	catch (NumberFormatException e) 
		{
			System.out.println("\nSession start time not available right now\n");
		} 
    	catch (IOException e) 
		{
			
			System.out.println("\nNot able to write to file at " + LOG_FILENAME + "\n");
		}
    	
    	//##########################################################################
    	
    	getBigPrimesFromFile();
    	
    	//even-odd + odd-even pairs
    	Trunk2TuplePrecursor(3, 2);
    	Trunk2TuplePrecursor(4, 1);
    	Trunk2TuplePrecursor(5, 2);
    	
    	//odd-odd pairs
    	Trunk2TuplePrecursor(5, 1);
    	Trunk2TuplePrecursor(5, 3);
    	Trunk2TuplePrecursor(7, 3);
    	
    	try {
			barrier.await();
    	}
		catch (InterruptedException e) 
		{
			synchronized(printLock) 
			{
				System.out.println("Thread waiting at barrier interrupted");
			}
		}
		catch (BrokenBarrierException e) 
		{
			synchronized(printLock) 
			{
				System.out.println("Barrier was broken unexpectedly");
			}
		}
    	
    	//find pairwise coprime 3-tuple
        generatePairwiseCoprime3Tuples();
        
        //##########################################################################
        
        today = new Date(System.currentTimeMillis());
    	timeString = formatter.format(today);
        
    	System.out.println("\n\nCalculations completed on " + timeString +
		 				   "\n#######################################################\n\n");
    	
        try {
			calculationLogWriter.write((new String("\n\nCalculations completed on " + timeString +
											 "\n########################################################\n\n")).getBytes());
			
			calculationLogWriter.flush();
		} 
        catch (IOException e) 
		{
			System.out.println("\nNot able to write to file at " + LOG_FILENAME + "\n");
		}
        
    	BCE.shutdown();
    }
    
	
	
    /*	
    private final void generatePairwiseCoprime3Tuples(final int m, final int n,
    												  final int m1, final int c1,
    												  final int n2, final int c2) 
    {
		if ((c1 == c2) && (m == m1) && (n == n2) && (c1 > n)) {
			synchronized(printLock) {
				System.out.println("Coprime 3-Tuple Found: " + m + "," + n + "," + c1);
			}
			
			try {
    			calculationLog.write((new String("\nCoprime 3-Tuple Found: " + m + "," + n + "," + c1)).getBytes());
    			
    			calculationLog.flush();
    		}
        	catch (IOException e) 
    		{
    			synchronized(printLock) 
    			{
    				System.out.println("\nNot able to write to file at " + FILENAME + "\n");
    			}
    		}
			
			testCoprime3Tuple(m, n, c1);
		}
		
		if ((m1 <= m) && (n2 <= n) && (c1 < MAX_NUM) && (c2 < MAX_NUM))
		{
			generate3Tuple(m, n, (m1 + c1), c1, (n2 + c2), c2);
			generate3Tuple(m, n, (m1 + c1), c1, n2, (c2 + n2));
			generate3Tuple(m, n, m1, (c1 + m1), (n2 + c2), c2);
			generate3Tuple(m, n, m1, (c1 + m1), n2, (c2 + n2));
		}
		*/
    }
}
