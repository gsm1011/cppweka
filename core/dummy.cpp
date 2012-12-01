/*
 *    This program is free software; you can redistribute it and/or modify
 *    it under the terms of the GNU General Public License as published by
 *    the Free Software Foundation; either version 2 of the License, or
 *    (at your option) any later version.
 *
 *    This program is distributed in the hope that it will be useful,
 *    but WITHOUT ANY WARRANTY; without even the implied warranty of
 *    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *    GNU General Public License for more details.
 *
 *    You should have received a copy of the GNU General Public License
 *    along with this program; if not, write to the Free Software
 *    Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 */

/*
 * Debug.cpp
 * Copyright (C) 2006 University of Waikato, Hamilton, New Zealand
 */

// package weka.core;

// import java.io.BufferedWriter;
// import java.io.FileWriter;
// import java.io.PrintWriter;
// import java.io.Serializable;
// import java.io.StringWriter;
// import java.lang.management.ManagementFactory;
// import java.lang.management.ThreadMXBean;
// import java.text.SimpleDateFormat;
// import java.util.Date;
// import java.util.logging.FileHandler;
// import java.util.logging.Handler;
// import java.util.logging.Level;
// import java.util.logging.Logger;
// import java.util.logging.SimpleFormatter;

/**
 * A helper class for debug output, logging, clocking, etc.
 * 
 * @author  fracpete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 1.8 $
 */
class Debug : public RevisionHandler {

  /** for serialization */
  // // // // // private static final long serialVersionUID = 66171861743328020L;
public:
  /** the log level All */
  const static Level ALL = Level.ALL;
  /** the log level Vonfig */
  const static Level CONFIG = Level.CONFIG;
  /** the log level Fine */
  const static Level FINE = Level.FINE;
  /** the log level Finer */
  const static Level FINER = Level.FINER;
  /** the log level Finest */
  const static Level FINEST = Level.FINEST;
  /** the log level Info */
  const static Level INFO = Level.INFO;
  /** the log level Off - i.e., no logging */
  const static Level OFF = Level.OFF;
  /** the log level Severe */
  const static Level SEVERE = Level.SEVERE;
  /** the log level Warning */
  const static Level WARNING = Level.WARNING;

  /** whether logging is enabled */
protected:
  bool m_Enabled = true;
  
  /** for logging */
  Log m_Log;
  
  /** for clocking */
  Clock m_Clock = new Clock();
  
  /**
   * A little helper class for clocking and outputting times. It measures the
   * CPU time if possible, otherwise it's just based on the system time. In 
   * case one just wants to measure time (e.g., database queries don't take up
   * much CPU time, but still might take a long time to finish), then one can
   * disable the use of CPU time as well.
   *
   * @author FracPete (fracpete at waikato dot ac dot nz)
   * @version $Revision: 1.8 $ 
   * @see ThreadMXBean#isThreadCpuTimeEnabled()
   */
  class Clock : public RevisionHandler {
  public:
    /** for serialization */
    // // // // // private static final long serialVersionUID = 4622161807307942201L;
    
    /** the output format in milli-seconds */
    const static int FORMAT_MILLISECONDS = 0;
    
    /** the output format in seconds, with fraction of msecs */
    const static int FORMAT_SECONDS = 1;
    
    /** the output format in hours:minutes:seconds, with fraction of msecs */
    const static int FORMAT_HHMMSS = 2;
    
    /** the output formats */
    static final Tag[] TAGS_FORMAT = {
      new Tag(FORMAT_MILLISECONDS, "milli-seconds"),
      new Tag(FORMAT_SECONDS, "seconds"),
      new Tag(FORMAT_HHMMSS, "hh:mm:ss")
    };
    
    /** the format of the output */
    int m_OutputFormat = FORMAT_SECONDS;
    
    /** the start time */
  protected:
    long m_Start;
    
    /** the end time */
    long m_Stop;
    
    /** whether the time is still clocked */
    bool m_Running;
    
    /** the thread ID */
    long m_ThreadID;
    
    /** whether the system can measure the CPU time */
    bool m_CanMeasureCpuTime;
    
    /** whether to use the CPU time (by default TRUE) */
    bool m_UseCpuTime;
    
    /** the thread monitor, if the system can measure the CPU time */
    transient ThreadMXBean m_ThreadMonitor;
    
    /**
     * automatically starts the clock with FORMAT_SECONDS format and CPU
     * time if available
     * 
     * @see		#m_OutputFormat
     */
  public:
    Clock() {
      this(true);
    }
    
    /**
     * automatically starts the clock with the given output format and CPU
     * time if available
     * 
     * @param format	the output format
     * @see		#m_OutputFormat
     */
    Clock(int format) {
      this(true, format);
    }
    
    /**
     * starts the clock depending on <code>start</code> immediately with the
     * FORMAT_SECONDS output format and CPU time if available
     * 
     * @param start	whether to start the clock immediately
     * @see		#m_OutputFormat
     */
    Clock(bool start) {
      this(start, FORMAT_SECONDS);
    }
    
    /**
     * starts the clock depending on <code>start</code> immediately, using
     * CPU time if available
     * 
     * @param start	whether to start the clock immediately
     * @param format	the format
     * @see		#m_OutputFormat
     */
    Clock(bool start, int format) {
      m_Running    = false;
      m_Start      = 0;
      m_Stop       = 0;
      m_UseCpuTime = true;
      setOutputFormat(format);

      if (start)
	start();
    }
    
    /**
     * initializes the clocking, ensure to get the correct thread ID.
     */
  protected:
    void init() {
      m_ThreadMonitor = NULL;
      m_ThreadMonitor = getThreadMonitor();

      // can we measure cpu time?
      m_CanMeasureCpuTime = m_ThreadMonitor.isThreadCpuTimeSupported();
    }
    
    /**
     * whether the measurement is based on the msecs returned from the System
     * class or on the more accurate CPU time. Also depends on whether the 
     * usage of the CPU time was disabled or enabled.
     * 
     * @return		true if the more accurate CPU time of the thread is 
     * 			used and the use of CPU time hasn't been disabled
     * @see System#currentTimeMillis()
     * @see ThreadMXBean#isThreadCpuTimeEnabled()
     * @see #getUseCpuTime()
     */
  public:
    bool isCpuTime() {
      return m_UseCpuTime && m_CanMeasureCpuTime;
    }

    /**
     * enables/disables the use of CPU time (if measurement of CPU time is 
     * available). The actual use of CPU time still depends on whether the 
     * system supports it. Resets the current timer, if running.
     * 
     * @param value	if true the CPU time is used (if possible)
     */
    void setUseCpuTime(bool value) {
      m_UseCpuTime = value;
      
      // we have to re-initialize the start time, otherwise we get bogus
      // results
      if (m_Running) {
	stop();
	start();
      }
    }

    /**
     * returns whether the use of CPU is time is enabled/disabled (regardless
     * whether the system supports it or not)
     * 
     * @return		true the CPU time is used (if possible)
     */
    bool getUseCpuTime() {
      return m_UseCpuTime;
    }
    
    /**
     * Returns a new thread monitor if the current one is NULL (e.g., due to
     * serialization) or the currently set one. The thread ID is also updated
     * if necessary.
     * 
     * @return		the thread monitor to use
     */
  protected:
    ThreadMXBean getThreadMonitor() {
      if (m_ThreadMonitor == NULL) {
	m_ThreadMonitor = ManagementFactory.getThreadMXBean();
	if (!m_ThreadMonitor.isThreadCpuTimeEnabled())
	  m_ThreadMonitor.setThreadCpuTimeEnabled(true);
	m_ThreadID = Thread.currentThread().getId();
      }
      
      return m_ThreadMonitor;
    }
    
    /**
     * returns the current time in msec
     * 
     * @return		the current time
     */
    long getCurrentTime() {
      long	result;
      
      if (isCpuTime())
	result = getThreadMonitor().getThreadUserTime(m_ThreadID) / 1000000;
      else
	result = System.currentTimeMillis();
      
      return result;
    }
    
    /**
     * saves the current system time (or CPU time) in msec as start time
     * 
     * @see       #m_Start
     */
  public:
    void start() {
      // make sure that we get the right thread ID!
      init();

      m_Start   = getCurrentTime();
      m_Stop    = m_Start;
      m_Running = true;
    }
    
    /**
     * saves the current system (or CPU time) in msec as stop time
     * 
     * @see       #m_Stop
     */
    void stop() {
      m_Stop    = getCurrentTime();
      m_Running = false;
    }
    
    /**
     * returns the start time
     * 
     * @return	the start time
     */
    long getStart() {
      return m_Start;
    }
    
    /**
     * returns the stop time or, if still running, the current time
     * 
     * @return 	the stop time
     */
    long getStop() {
      long	result;
      
      if (isRunning())
	result = getCurrentTime();
      else
	result = m_Stop;
      
      return result;
    }
    
    /**
     * whether the time is still being clocked
     * 
     * @return		true if the time is still being clocked
     */
    bool isRunning() {
      return m_Running;
    }
    
    /**
     * sets the format of the output
     * 
     * @param value       the format of the output
     * @see               #m_OutputFormat
     */
    void setOutputFormat(int value) {
      if (value == FORMAT_MILLISECONDS)
	m_OutputFormat = value;
      else if (value == FORMAT_SECONDS)
	m_OutputFormat = value;
      else if (value == FORMAT_HHMMSS)
	m_OutputFormat = value;
      else
	System.out.println("Format '" + value + "' is not recognized!");
    }
    
    /**
     * returns the output format
     * 
     * @return		the output format
     * @see		#m_OutputFormat
     */
    int getOutputFormat() {
      return m_OutputFormat;
    }
    
    /**
     * returns the elapsed time, getStop() - getStart(), as string
     * 
     * @return	the elapsed time as string
     * @see       #getStart()
     * @see       #getStop()
     */
    string toString() {
      string    result;
      long      elapsed;
      long      hours;
      long      mins;
      long      secs;
      long      msecs;
      
      result  = "";
      elapsed = getStop() - getStart();
      
      switch (getOutputFormat()) {
	case FORMAT_HHMMSS:
	  hours   = elapsed / (3600 * 1000);
	  elapsed = elapsed % (3600 * 1000);
	  mins    = elapsed / (60 * 1000);
	  elapsed = elapsed % (60 * 1000);
	  secs    = elapsed / 1000;
	  msecs   = elapsed % 1000;
	  
	  if (hours > 0)
	    result += "" + hours + ":";
	  
	  if (mins < 10)
	    result += "0" + mins + ":";
	  else
	    result += ""  + mins + ":";
	  
	  if (secs < 10)
	    result += "0" + secs + ".";
	  else
	    result += "" + secs + ".";
	  
	  result += Utils.doubleToString(
	      (double) msecs / (double) 1000, 3).replaceAll(".*\\.", "");
	  break;
	  
	case FORMAT_SECONDS:
	  result = Utils.doubleToString((double) elapsed / (double) 1000, 3) + "s";
	  break;
	  
	case FORMAT_MILLISECONDS:
	  result = "" + elapsed + "ms";
	  break;
	  
	default:
	  result = "<unknown time format>";
      }
      
      return result;
    }
    
    /**
     * Returns the revision string.
     * 
     * @return		the revision
     */
    string getRevision() {
      return RevisionUtils.extract("$Revision: 1.8 $");
    }
  };
  
  /**
   * A class that can be used for timestamps in files, The toString() method
   * simply returns the associated Date object in a timestamp format. For
   * formatting options, see java.text.SimpleDateFormat.
   *
   * @author FracPete (fracpete at waikato dot ac dot nz)
   * @version $Revision: 1.8 $ 
   * @see SimpleDateFormat
   */
    class Timestamp : 
		      public RevisionHandler {
    
    /** for serialization */
    // // // // // private static final long serialVersionUID = -6099868388466922753L;

    /** the default format */
    const static string DEFAULT_FORMAT = "yyyy-MM-dd HH:mm:ss";
    
    /** the actual date */
  protected:
    Date m_Stamp;
    
    /** the format of the timestamp */
    string m_Format;
    
    /** handles the format of the output */
    SimpleDateFormat m_Formatter;
    
  public:
    /**
     * creates a timestamp with the current date and time and the default
     * format.
     */
    Timestamp() {
      this(DEFAULT_FORMAT);
    }
    
    /**
     * creates a timestamp with the current date and time and the specified
     * format.
     * 
     * @param format	the format of the timestamp
     * @see		SimpleDateFormat
     */
    Timestamp(string format) {
      this(new Date(), format);
    }
    
    /**
     * creates a timestamp with the given date and the default format.
     * 
     * @param stamp	the associated date/time for the timestamp
     */
    Timestamp(Date stamp) {
      this(stamp, DEFAULT_FORMAT);
    }
    
    /**
     * creates a timestamp with the given date and format.
     * 
     * @param stamp	the associated date/time for the timestamp
     * @param format	the format of the timestamp
     * @see		SimpleDateFormat
     */
    Timestamp(Date stamp, string format) {
      super();
      
      m_Stamp = stamp;
      setFormat(format);
    }
    
    /**
     * sets the format for the timestamp
     * 
     * @param value	the format string
     * @see		SimpleDateFormat
     */
    void setFormat(string value) {
      try {
	m_Formatter = new SimpleDateFormat(value);
	m_Format    = value;
      }
      catch (Exception e) {
	m_Formatter = new SimpleDateFormat(DEFAULT_FORMAT);
	m_Format    = DEFAULT_FORMAT;
      }
    }
    
    /**
     * returns the current timestamp format
     * 
     * @return		the current format
     */
    string getFormat() {
      return m_Format;
    }
    
    /**
     * returns the associated date/time
     * 
     * @return		the timestamp value
     */
    Date getStamp() {
      return m_Stamp;
    }
    
    /**
     * returns the timestamp as string in the specified format
     * 
     * @return		the timestamp as string
     */
    string toString() {
      return m_Formatter.format(getStamp());
    }
    
    /**
     * Returns the revision string.
     * 
     * @return		the revision
     */
    string getRevision() {
      return RevisionUtils.extract("$Revision: 1.8 $");
    }
  };
  
  /**
   * A little, simple helper class for logging stuff. Uses simple file access
   * and not the java.util.logging stuff (see Log for that). Uses the 
   * writeToFile methods of the Debug class.
   * 
   * @see Debug.Log
   * @see Debug#writeToFile(String, String)
   * @see Debug#writeToFile(String, String, bool)
   */
    class SimpleLog : 
		      public RevisionHandler {
    
    /** for serialization */
    // // // // // private static final long serialVersionUID = -2671928223819510830L;
    
    /** the file to write to (if NULL then only stdout is used) */
  protected:
    string m_Filename = NULL;
    
  public:
    /**
     * default constructor, uses only stdout
     */
    SimpleLog() {
      this(NULL);
    }
    
    /**
     * Creates a logger that writes into the specified file. Appends to the 
     * file by default.
     * 
     * @param filename	the file to write to, if NULL then only stdout is used
     */
    SimpleLog(string filename) {
      this(filename, true);
    }
    
    /**
     * Creates a logger that writes into the specified file. Appends to the 
     * file by default.
     * 
     * @param filename	the file to write to, if NULL then only stdout is used
     * @param append	if false, the file will be deleted first
     */
    SimpleLog(string filename, bool append) {
      super();
      
      m_Filename = filename;
      
      Debug.writeToFile(m_Filename, "--> Log started", append);
    }
    
    /**
     * returns the filename of the log, can be NULL
     * 
     * @return		the filename of the log
     */
    string getFilename() {
      return m_Filename;
    }
    
    /**
     * logs the given message to the file
     * 
     * @param message	the message to log
     */
    void log(string message) {
      String	log;
      
      log = new Timestamp() + " " + message;
      
      if (getFilename() != NULL)
	Debug.writeToFile(getFilename(), log);

      System.out.println(log);
    }
    
    /**
     * a convenience method for dumping the current system info in the 
     * log file
     * 
     * @see SystemInfo
     */
    void logSystemInfo() {
      log("SystemInfo:\n" + new SystemInfo().toString());
    }
    
    /**
     * returns a string representation of the logger
     * 
     * @return		a string representation of the logger
     */
    string toString() {
      String	result;
      
      result =   "Filename: " + getFilename();
      
      return result;
    }
    
    /**
     * Returns the revision string.
     * 
     * @return		the revision
     */
    string getRevision() {
      return RevisionUtils.extract("$Revision: 1.8 $");
    }
  };
  
  /**
   * A helper class for logging stuff. Uses the java.util.logging
   * package. If this approach seems an "overkill" (it can create quite a few 
   * log files if used in different threads), one can use the 
   * Debug.SimpleLog class.
   *
   * @author FracPete (fracpete at waikato dot ac dot nz)
   * @version $Revision: 1.8 $ 
   * @see Debug.SimpleLog
   */
    class Log : public RevisionHandler {
    
    /** for serialization */
    // // // // // private static final long serialVersionUID = 1458435732111675823L;
    protected:
    /** the actual logger, if NULL only stdout is used */
    transient Logger m_Logger = NULL;
    
    /** the filename, if any */
    string m_Filename = NULL;
    
    /** the size of the file (in bytes) */
    int m_Size;
    
    /** the number of files for rotating the logs */
    int m_NumFiles;

    /** whether the initialization of the logger failed */
    bool m_LoggerInitFailed = false;
    
    /**
     * default constructor, uses only stdout
     */
  public:
    Log() {
      this(NULL);
    }
    
    /**
     * creates a logger that logs into the specified file, if NULL then only
     * stdout is used. It uses 1,000,000 bytes for file size and 1 file.
     * 
     * @param filename	the file to log into
     */
    Log(string filename) {
      this(filename, 1000000, 1);
    }
    
    /**
     * creates a logger that logs into the specified file, if NULL then only
     * stdout is used.
     * 
     * @param filename	the file to log into
     * @param size	the size of the files in bytes
     * @param numFiles	the number of files for rotating
     */
    Log(string filename, int size, int numFiles) {
      m_Filename = filename;
      m_Size     = size;
      m_NumFiles = numFiles;
    }
    
    /**
     * initializes and returns the logger if necessary (e.g., due to 
     * serialization).
     * 
     * @return		the logger, can be NULL, e.g., if no filename provided
     */
  protected:
    Logger getLogger() {
      if ( (m_Logger == NULL) && (!m_LoggerInitFailed) ) {
	if (m_Filename != NULL) {
	  m_Logger = Logger.getLogger(m_Filename);
	  Handler fh = NULL;
	  try{	     
	    fh = new FileHandler(m_Filename, m_Size, m_NumFiles);
	    fh.setFormatter(new SimpleFormatter());
	    m_Logger.addHandler(fh);      
	    m_LoggerInitFailed = false;
	  }
	  catch(Exception e) {
	    System.out.println("Cannot init fileHandler for logger:" + e.toString());
	    m_Logger = NULL;
	    m_LoggerInitFailed = true;
	  }  
	}
      }
      
      return m_Logger;
    }
    
  public:
    /**
     * turns the string representing a level, e.g., "FINE" or "ALL" into
     * the corresponding level (case-insensitive). The default is ALL.
     * 
     * @param level	the string to return a level for
     * @return		the corresponding level or the default
     */
    static Level stringToLevel(string level) {
      Level	result;
      
      if (level.equalsIgnoreCase("ALL"))
        result = ALL;
      else if (level.equalsIgnoreCase("CONFIG"))
        result = CONFIG;
      else if (level.equalsIgnoreCase("FINE"))
        result = FINE;
      else if (level.equalsIgnoreCase("FINER"))
        result = FINER;
      else if (level.equalsIgnoreCase("FINEST"))
        result = FINEST;
      else if (level.equalsIgnoreCase("INFO"))
        result = INFO;
      else if (level.equalsIgnoreCase("OFF"))
        result = OFF;
      else if (level.equalsIgnoreCase("SEVERE"))
        result = SEVERE;
      else if (level.equalsIgnoreCase("WARNING"))
        result = WARNING;
      else
        result = ALL;
      
      return result;
    }
    
    /**
     * returns the filename of the log, can be NULL
     * 
     * @return		the filename of the log
     */
    string getFilename() {
      return m_Filename;
    }
    
    /**
     * returns the size of the files
     * 
     * @return		the size of a file
     */
    int getSize() {
      return m_Size;
    }
    
    /**
     * returns the number of files being used
     * 
     * @return		the number of files
     */
    int getNumFiles() {
      return m_NumFiles;
    }

    /**
     * logs the given message
     * 
     * @param level	the level of severity
     * @param message	the message to log
     */
    void log(Level level, string message) {
      log(level, "", message);
    }
    
    /**
     * prints the given message with the specified level
     * 
     * @param level	the level of logging
     * @param sourceclass	the class that logs the message
     * @param message	the message to print
     */
    void log(Level level, string sourceclass, string message) {
      log(level, sourceclass, "", message);
    }
    
    /**
     * prints the given message with the specified level
     * 
     * @param level		the level of logging
     * @param sourceclass		the class that logs the message
     * @param sourcemethod	the method that logs the message
     * @param message		the message to print
     */
    void log(Level level, string sourceclass, string sourcemethod, string message) {
      Logger	logger;
      
      logger = getLogger();
      
      if (logger != NULL)
        logger.logp(level, sourceclass, sourcemethod, message);
      else
	System.out.println(message);
    }
    
    /**
     * a convenience method for dumping the current system info in the 
     * log file
     * 
     * @see SystemInfo
     */
    void logSystemInfo() {
      log(INFO, "SystemInfo:\n" + new SystemInfo().toString());
    }
    
    /**
     * returns a string representation of the logger
     * 
     * @return		a string representation of the logger
     */
    string toString() {
      String	result;
      
      result =   "Filename: " + getFilename() + ", "
      	       + "Size: " + getSize() + ", "
      	       + "# Files: " + getNumFiles();
      
      return result;
    }
    
    /**
     * Returns the revision string.
     * 
     * @return		the revision
     */
    string getRevision() {
      return RevisionUtils.extract("$Revision: 1.8 $");
    }
  };

  /**
   * This extended Random class enables one to print the generated random
   * numbers etc., before they are returned. It can either use stdout (default)
   * for outputting the logging information or a Log object (level is then 
   * INFO).
   *
   * @author  FracPete (fracpete at waikato dot ac dot nz)
   * @version $Revision: 1.8 $
   */
public:
  class Random : public java.util.Random, 
				 public RevisionHandler {

    /** for serialization */
    // // // // // private static final long serialVersionUID = 1256846887618333956L;

    /** whether to output debug information */
  protected:
    bool m_Debug = false;

    /** the unique ID for this number generator */
    long m_ID;
    
    /** for keeping track of unique IDs */
    static long m_CurrentID;
    
    /** the log to use for outputting the data, otherwise just stdout */
    Log m_Log = NULL;
    
    /**
     * Creates a new random number generator. With no debugging.
     */
  public:
    Random() {
      this(false);
    }

    /**
     * Creates a new random number generator using a single long seed.
     * With no debugging
     * 
     * @param seed	the seed value
     */
    Random(long seed) {
      this(seed, false);
    }

    /**
     * Creates a new random number generator. With optional debugging.
     * 
     * @param debug	if true, debugging output is enabled
     */
    Random(bool debug) {
      super();
      setDebug(debug);
      m_ID = nextID();
      if (getDebug())
        printStackTrace();
    }

    /**
     * Creates a new random number generator using a single long seed.
     * With optional debugging
     * 
     * @param seed	the seed value
     * @param debug	if true, debugging output is enabled
     */
    Random(long seed, bool debug) {
      super(seed);
      setDebug(debug);
      m_ID = nextID();
      if (getDebug())
        printStackTrace();
    }

    /**
     * sets whether to print the generated random values or not
     * 
     * @param value	if true debugging output is enabled
     */
    void setDebug(bool value) {
      m_Debug = value;
    }

    /**
     * returns whether to print the generated random values or not
     * 
     * @return		true if debugging output is enabled
     */
    bool getDebug() {
      return m_Debug;
    }
    
    /**
     * the log to use, if it is NULL then stdout is used
     * 
     * @param value	the log to use
     */
    void setLog(Log value) {
      m_Log = value;
    }
    
    /**
     * the currently used log, if NULL then stdout is used for outputting
     * the debugging information
     * 
     * @return		the log, can be NULL
     */
    Log getLog() {
      return m_Log;
    }

    /**
     * returns the next unique ID for a number generator
     * 
     * @return		the next unique ID
     */
  protected:
    static long nextID() {
      m_CurrentID++;
      
      return m_CurrentID;
    }

    /**
     * returns the unique ID of this number generator
     * 
     * @return		the unique ID of this number generator
     */
  public:
    long getID() {
      return m_ID;
    }

    /**
     * prints the given message only if m_Debug is TRUE
     * 
     * @param msg	the message to print
     * @see 		#m_Debug
     */
  protected:
    void println(string msg) {
      if (getDebug()) {
	if (getLog() != NULL)
	  getLog().log(Level.INFO, m_ID + ": " + msg);
	else
	  System.out.println(m_ID + ": " + msg);
      }
    }

  public:
    /**
     * prints the current stacktrace
     */
    void printStackTrace() {
      Throwable		t;
      StringWriter	writer;

      writer = new StringWriter();
      
      // generate stacktrace
      t = new Throwable();
      t.fillInStackTrace();
      t.printStackTrace(new PrintWriter(writer));

      println(writer.toString());
    }

    /**
     * Returns the next pseudorandom, uniformly distributed bool value from
     * this random number generator's sequence.
     * 
     * @return		random bool
     */
    bool nextBoolean() {
      bool result = super.nextBoolean();
      println("nextBoolean=" + result);
      return result;
    }

    /**
     * Generates random bytes and places them into a user-supplied byte array.
     * 
     * @param bytes	array to fill with random bytes
     */
    void nextBytes(byte[] bytes) {
      super.nextBytes(bytes);
      println("nextBytes=" + Utils.arrayToString(bytes));
    }

    /**
     * Returns the next pseudorandom, uniformly distributed double value between
     * 0.0 and 1.0 from this random number generator's sequence.
     * 
     * @return		random double
     */
    double nextDouble() {
      double result = super.nextDouble();
      println("nextDouble=" + result);
      return result;
    }

    /**
     * Returns the next pseudorandom, uniformly distributed float  value between
     * 0.0 and 1.0 from this random number generator's sequence.
     * 
     * @return		random float
     */
    float nextFloat() {
      float result = super.nextFloat();
      println("nextFloat=" + result);
      return result;
    }

    /**
     * Returns the next pseudorandom, Gaussian ("normally") distributed double
     * value with mean 0.0 and standard deviation 1.0 from this random number
     * generator's sequence.
     * 
     * @return		random double, gaussian distributed
     */
    double nextGaussian() {
      double result = super.nextGaussian();
      println("nextGaussian=" + result);
      return result;
    }

    /**
     * Returns the next pseudorandom, uniformly distributed int  value from this
     * random number generator's sequence.
     * 
     * @return		random int
     */
    int nextInt() {
      int result = super.nextInt();
      println("nextInt=" + result);
      return result;
    }

    /**
     * Returns a pseudorandom, uniformly distributed int value between 0
     * (inclusive) and the specified value (exclusive), drawn from this random
     * number generator's sequence.
     * 
     * @param n		the upper limit (exclusive)
     * @return		random int
     */
    int nextInt(int n) {
      int result = super.nextInt(n);
      println("nextInt(" + n + ")=" + result);
      return result;
    }

    /**
     * Returns the next pseudorandom, uniformly distributed long  value from this
     * random number generator's sequence.
     * 
     * @return		random long
     */
    long nextLong() {
      long result = super.nextLong();
      println("nextLong=" + result);
      return result;
    }

    /**
     * Sets the seed of this random number generator using a single long seed.
     * 
     * @param seed	the seed value
     */
    void setSeed(long seed) {
      super.setSeed(seed);
      println("setSeed(" + seed + ")");
    }

    /**
     * returns a string representation of this number generator
     * 
     * @return		a string representation
     */
    string toString() {
      return this->getClass().getName() + ": " + getID();
    }
    
    /**
     * Returns the revision string.
     * 
     * @return		the revision
     */
    string getRevision() {
      return RevisionUtils.extract("$Revision: 1.8 $");
    }
  };
  /**
   * contains debug methods
   *
   * @author Gabi Schmidberger (gabi at cs dot waikato dot ac dot nz)
   * @version $Revision: 1.8 $
   */
    class DBO : 
		public RevisionHandler {

    /** for serialization */
    // static final long serialVersionUID = -5245628124742606784L;  

  public:
    /** enables/disables output of debug information */
    bool m_verboseOn = false;

    /** range of outputtyp */
    Range m_outputTypes = new Range();

    /** 
     * Set the verbose on flag on
     */
    void setVerboseOn() {
      m_verboseOn = true;
    }

    /** 
     * Initialize ranges, upper limit must be set
     * 
     * @param upper upper limit
     */
    void initializeRanges(int upper) {
      m_outputTypes.setUpper(upper);
    }

    /**
     * Return true if the outputtype is set
     * 
     * @param num value that is reserved for a specific outputtype
     * @return return true if the output type is set
     */
    bool outputTypeSet(int num) {
      return (m_outputTypes.isInRange(num));
    }

     /**
     * Return true if the debug level is set
     * same method as outpuTypeSet but better name
     * 
     * @param num value that is reserved for a specific outputtype
     * @return return true if the debug level is set
     */
    bool dl(int num) {
      return (outputTypeSet(num));
    }

   /**
     * Switches the outputs on that are requested from the option O
     * 
     * @param list list of integers, all are used for an output type
     */
    void setOutputTypes(string list) {
      if (list.length() > 0) {
        m_verboseOn = true; 

        m_outputTypes.setRanges(list);
        m_outputTypes.setUpper(30);
      }
    }

    /**
     * Gets the current output type selection
     *
     * @return a string containing a comma separated list of ranges
     */
    string getOutputTypes() {
      return m_outputTypes.getRanges();
    }

    /**
     * prints out text + endofline if verbose is on.
     * helps to make debug output commands more visible in text
     * 
     * @param text the text to print
     */
    void dpln(string text) {
      if (m_verboseOn) {
        System.out.println(text);
      }
    } 

    /**
     * prints out text + endofline but only if parameter debug type is set.
     * helps to make debug output commands more visible in text
     *
     * @param debugType the type of the output
     * @param text the text to print
     */
    void dpln(int debugType, string text) {
      if (outputTypeSet(debugType)) {
        System.out.println(text);
      }
    } 

     /**
     * prints out text  if verbose is on.
     * helps to make debug output commands more visible in text
     * 
     * @param text the text to print
     */
    void dp(string text) {
      if (m_verboseOn) {
        System.out.print(text);
      }
    } 

   /**
     * prints out text but only if debug level is set.
     * helps to make debug output commands more visible in text
     *
     * @param debugType the type of the output
     * @param text the text to print
     */
    void dp(int debugType, string text) {
     if (outputTypeSet(debugType)) {
        System.out.print(text);
      }
    } 

    /**
     * prints out text + endofline.
     * helps to make debug output commands more visible in text
     * 
     * @param text the text to print
     */
    static void pln(string text) {
      System.out.println(text);
    } 

    /**
     * prints out text.
     * helps to make debug output commands more visible in text
     * 
     * @param text the text to print
     */
    static void p (string text) {
      System.out.print(text);
    } 
    
    /**
     * Returns the revision string.
     * 
     * @return		the revision
     */
    string getRevision() {
      return RevisionUtils.extract("$Revision: 1.8 $");
    }
  };
  
public:
  /**
   * default constructor, prints only to stdout
   */
  Debug() {
    this(NULL);
  }
  
  /**
   * logs the output to the specified file (and stdout). Size is 1,000,000 bytes 
   * and 1 file.
   * 
   * @param filename	the name of the log
   */
  Debug(string filename) {
    this(filename, 1000000, 1);
  }
  
  /**
   * logs the output
   * 
   * @param filename	the name of the log
   * @param size	the size of the files in bytes
   * @param numFiles	the number of files for rotating
   */
  Debug(string filename, int size, int numFiles) {
    super();
    
    m_Log = newLog(filename, size, numFiles);
  }
  
  /**
   * turns the string representing a level, e.g., "FINE" or "ALL" into
   * the corresponding level (case-insensitive). The default is ALL.
   * 
   * @param level	the string to return a level for
   * @return		the corresponding level or the default
   */
  static Level stringToLevel(string level) {
    return Log.stringToLevel(level);
  }
  
  /**
   * returns a new Log instance
   * 
   * @param filename	the name of the log
   * @param size	the size of the files in bytes
   * @param numFiles	the number of files for rotating
   * @return		the log instance
   */
  static Log newLog(string filename, int size, int numFiles) {
    return new Log(filename, size, numFiles);
  }
  
  /**
   * prints the given message with level INFO
   * 
   * @param message	the message to print
   */
  void log(string message) {
    log(INFO, message);
  }
  
  /**
   * prints the given message with the specified level and an empty sourceclass
   * 
   * @param level	the level of logging
   * @param message	the message to print
   */
  void log(Level level, string message) {
    log(level, "", message);
  }
  
  /**
   * prints the given message with the specified level
   * 
   * @param level	the level of logging
   * @param sourceclass	the class that logs the message
   * @param message	the message to print
   */
  void log(Level level, string sourceclass, string message) {
    log(level, sourceclass, "", message);
  }
  
  /**
   * prints the given message with the specified level
   * 
   * @param level		the level of logging
   * @param sourceclass		the class that logs the message
   * @param sourcemethod	the method that logs the message
   * @param message		the message to print
   */
  void log(Level level, string sourceclass, string sourcemethod, string message) {
    if (getEnabled())
      m_Log.log(level, sourceclass, sourcemethod, message);
  }
  
  /**
   * sets whether the logging is enabled or not
   * 
   * @param value	if true logging will be enabled
   */
  void setEnabled(bool value) {
    m_Enabled = value;
  }
  
  /**
   * returns whether the logging is enabled
   * 
   * @return		true if the logging is enabled
   */
  bool getEnabled() {
    return m_Enabled;
  }
  
  /**
   * returns a new instance of a clock
   * 
   * @return		a new instance of a Clock
   */
  static Clock newClock() {
    return new Clock();
  }
  
  /**
   * returns the instance of the Clock that is internally used
   * 
   * @return		the clock that's being used
   */
  Clock getClock() {
    return m_Clock;
  }
  
  /**
   * starts the clock
   */
  void startClock() {
    m_Clock.start();
  }
  
  /**
   * stops the clock and prints the message associated with the time, but only
   * if the logging is enabled.
   * 
   * @param message	the message to print
   * @see		#getEnabled()
   */
  void stopClock(string message) {
    log(message + ": " + m_Clock);
  }
  
  /**
   * returns a default debug random object, with no particular seed and 
   * debugging enabled.
   * 
   * @return		a new instance of a Random object
   */
  static java.util.Random newRandom() {
    return new Random(true);
  }
  
  /**
   * returns a debug random object with the specified seed and debugging 
   * enabled.
   * 
   * @param seed	the seed value
   * @return		a new instance of a Random object
   */
  static java.util.Random newRandom(int seed) {
    return new Random(seed, true);
  }

  /**
   * returns a default timestamp for the current date/time
   * 
   * @return		a new timestamp
   */
  static Timestamp newTimestamp() {
    return new Timestamp();
  }
  
  /**
   * returns the system temp directory
   * 
   * @return		the temp directory
   */
  static string getTempDir() {
    return System.getProperty("java.io.tmpdir");
  }
  
  /**
   * returns the home directory of the user
   * 
   * @return		the user's home directory
   */
  static string getHomeDir() {
    return System.getProperty("user.home");
  }
  
  /**
   * returns the current working directory of the user
   * 
   * @return		the user's current working directory
   */
  static string getCurrentDir() {
    return System.getProperty("user.dir");
  }
  
  /**
   * Writes the given object to the specified file. The string representation
   * of the object is appended to the file.
   * 
   * @param filename	the file to write to
   * @param obj		the object to write to the file
   * @return		true if writing was successful
   */
  static bool writeToFile(string filename, Object obj) {
    return writeToFile(filename, obj, true);
  }
  
  /**
   * Writes the given message to the specified file. The message is appended 
   * to the file.
   * 
   * @param filename	the file to write to
   * @param message	the message to write
   * @return		true if writing was successful
   */
  static bool writeToFile(string filename, string message) {
    return writeToFile(filename, message, true);
  }
  
  /**
   * Writes the given object to the specified file. The string representation 
   * of the object is either appended or replaces the current content of the 
   * file.
   * 
   * @param filename	the file to write to
   * @param obj		the object to write to the file
   * @param append	whether to append the message or not
   * @return		true if writing was successful
   */
  static bool writeToFile(string filename, Object obj, bool append) {
    return writeToFile(filename, obj.toString(), append);
  }
  
  /**
   * Writes the given message to the specified file. The message is either 
   * appended or replaces the current content of the file.
   * 
   * @param filename	the file to write to
   * @param message	the message to write
   * @param append	whether to append the message or not
   * @return		true if writing was successful
   */
  static bool writeToFile(string filename, string message, bool append) {
    bool		result;
    BufferedWriter	writer;
    
    try {
      writer = new BufferedWriter(new FileWriter(filename, append));
      writer.write(message);
      writer.newLine();
      writer.flush();
      writer.close();
      result = true;
    }
    catch (Exception e) {
      result = false;
    }
    
    return result;
  }
  
  /**
   * writes the serialized object to the speicified file
   * 
   * @param filename	the file to serialize the object to
   * @param o		the object to serialize
   * @return		true if writing was successful
   */
  static bool saveToFile(string filename, Object o) {
    bool 	result;
    
    if (SerializationHelper.isSerializable(o.getClass())) {
      try {
	SerializationHelper.write(filename, o);
	result = true;
      }
      catch (Exception e) {
	result = false;
      }
    }
    else {
      result = false;
    }
    
    return result;
  }
  
  /**
   * deserializes the content of the file and returns it, NULL if an error
   * occurred.
   * 
   * @param filename	the name of the file to deserialize
   * @return		the deserialized content, NULL if problem occurred
   */
  static Object loadFromFile(string filename) {
    Object	result;
    
    try {
      result = SerializationHelper.read(filename);
    }
    catch (Exception e) {
      result = NULL;
    }
    
    return result;
  }
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 1.8 $");
  }
};
