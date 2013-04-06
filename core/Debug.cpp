#include "Debug.hpp"

Clock::Clock(bool start, int format) {
    m_Running    = false;
    m_Start      = 0;
    m_Stop       = 0;
    m_UseCpuTime = true;
    setOutputFormat(format);

    if (start)
	start();
}
    
void Clock::init() {
    m_ThreadMonitor = NULL;
    m_ThreadMonitor = getThreadMonitor();

    // can we measure cpu time?
    m_CanMeasureCpuTime = m_ThreadMonitor.isThreadCpuTimeSupported();
}
    
void Clock::setUseCpuTime(bool value) {
    m_UseCpuTime = value;
      
    // we have to re-initialize the start time, otherwise we get bogus
    // results
    if (m_Running) {
	stop();
	start();
    }
}

ThreadMXBean Clock::getThreadMonitor() {
    if (m_ThreadMonitor == NULL) {
	m_ThreadMonitor = ManagementFactory.getThreadMXBean();
	if (!m_ThreadMonitor.isThreadCpuTimeEnabled())
	    m_ThreadMonitor.setThreadCpuTimeEnabled(true);
	m_ThreadID = Thread.currentThread().getId();
    }
      
    return m_ThreadMonitor;
}
    
long Clock::getCurrentTime() {
    long	result;
      
    if (isCpuTime())
	result = getThreadMonitor().getThreadUserTime(m_ThreadID) / 1000000;
    else
	result = System.currentTimeMillis();
      
    return result;
}
    
void Clock::start() {
    // make sure that we get the right thread ID!
    init();

    m_Start   = getCurrentTime();
    m_Stop    = m_Start;
    m_Running = true;
}
    
long Clock::getStop() {
    long	result;
      
    if (isRunning())
	result = getCurrentTime();
    else
	result = m_Stop;
      
    return result;
}
    
string Clock::toString() {
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
    
Timestamp::Timestamp(Date stamp) {
    this(stamp, DEFAULT_FORMAT);
}

Timestamp::Timestamp(Date stamp, string format) {
    super();
      
    m_Stamp = stamp;
    setFormat(format);
}
    
void Timestamp::setFormat(string value) {
    try {
	m_Formatter = new SimpleDateFormat(value);
	m_Format    = value;
    }
    catch (Exception e) {
	m_Formatter = new SimpleDateFormat(DEFAULT_FORMAT);
	m_Format    = DEFAULT_FORMAT;
    }
}
    
SimpleLog::SimpleLog(string filename, bool append) {
    super();
      
    m_Filename = filename;
      
    Debug.writeToFile(m_Filename, "--> Log started", append);
}
    
void SimpleLog::log(string message) {
    String	log;
      
    log = new Timestamp() + " " + message;
      
    if (getFilename() != NULL)
	Debug.writeToFile(getFilename(), log);

    System.out.println(log);
}

Logger Log::getLogger() {
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
    
static Level Log::stringToLevel(string level) {
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
    
void Log::log(Level level, string sourceclass, string sourcemethod, string message) {
    Logger	logger;
      
    logger = getLogger();
      
    if (logger != NULL)
        logger.logp(level, sourceclass, sourcemethod, message);
    else
	System.out.println(message);
}
    
Random::Random(bool debug) {
    super();
    setDebug(debug);
    m_ID = nextID();
    if (getDebug())
        printStackTrace();
}

Random::Random(long seed, bool debug) {
    super(seed);
    setDebug(debug);
    m_ID = nextID();
    if (getDebug())
        printStackTrace();
}

void Random::printStackTrace() {
    Throwable		t;
    StringWriter	writer;

    writer = new StringWriter();
      
    // generate stacktrace
    t = new Throwable();
    t.fillInStackTrace();
    t.printStackTrace(new PrintWriter(writer));

    println(writer.toString());
}

static bool Debug::writeToFile(string filename, string message, bool append) {
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
  
static bool Debug::saveToFile(string filename, Object o) {
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
  
static Object Debug::loadFromFile(string filename) {
    Object	result;
    
    try {
	result = SerializationHelper.read(filename);
    }
    catch (Exception e) {
	result = NULL;
    }
    
    return result;
}
