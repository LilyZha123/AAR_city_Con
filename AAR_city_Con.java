import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.ConnectException;
import java.net.NoRouteToHostException;
import java.net.URL;
import java.net.URLConnection;
import java.net.UnknownHostException;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Properties;
import java.util.TimeZone;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

//import oracle.net.TNSAddress.Description;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.apache.log4j.PropertyConfigurator;

import com.trafficcast.base.dbutils.DBConnector;
import com.trafficcast.base.dbutils.DBUtils;
import com.trafficcast.base.enums.EventType;
import com.trafficcast.base.geocoding.MySqlGeocodingEngine;
import com.trafficcast.base.geocoding.MySqlGeocodingInitiater;
import com.trafficcast.base.inccon.IncConDBUtils;
import com.trafficcast.base.inccon.IncConRecord;
import com.trafficcast.base.tctime.TCTime;

/*************************************************************************************
 * <p>
 * HOU_tanstarXML_IncCon.java
 * -------------------------
 * Copyright (c) 2015 Trafficcast International Inc. All rights reserved.
 * <p>
 *  This reader is created by ticket #8498, it is used to archive IncCon record and save them into table.
 * <p>
 * --------------------------------------------------------
 * @author Carson Lee
 * @version 1.0
 * @since 1.5
 * --------------------------------------------------------
 * Change history
 * --------------------------------------------------------
 * Change number : #1
 * Programmer    : Harry Yang
 * Date          : 08/09/2017
 * Description   : created by ticket #8618, Modify street name for TT map
 * --------------------------------------------------------
 * Change number : #2
 * Ticket number : #SD-610
 * Programmer    : Lily Zha
 * Date          : 11/03/2018
 * Description   : data parsing review and new format
 * --------------------------------------------------------
 * Change number : #3
 * Ticket number : #SD-795
 * Programmer    : Lily Zha
 * Date          : 2/22/2019
 * Description   : clean up html tags</LI> <LI> in description
 * --------------------------------------------------------
 * Change number : #4
 * Ticket number : #SD-806
 * Programmer    : Lily Zha
 * Date          : 2/28/2019
 * Description   : clean up html tags</LI> <LI> in description
 * --------------------------------------------------------
 * Change number : #5
 * Ticket number : #SD-857
 * Programmer    : Lily Zha
 * Date          : 4/8/2019
 * Description   : clean up html tags</LI> <LI> in description
 * --------------------------------------------------------
 * Change number : #6
 * Ticket number : #SD-907,#SD-940
 * Programmer    : Lily Zha
 * Date          : 5/17/2019
 * Description   : solve '' is not a valid direction code problem
 * --------------------------------------------------------
 * Change number : #6
 * Ticket number : #SD-1066
 * Programmer    : Jason
 * Date          : 8/27/2019
 * Description   : Current Time Use, need type 1 for special event reports and improve parsing
 * --------------------------------------------------------
 * Change number : #8
 * Ticket number : #SD-1229
 * Programmer    : Lily Zha
 * Date          : 11/7/2019
 * Description   : "End time may NOT be null" repeating error
 *************************************************************************************/
public class AAR_city_Con {
    // Current version of this class.
    public static final double VERSION = 1.0;
    
    //Property file location
    private final String PROPERTY_FILE = "prop/AAR_city_Con.properties";
    private final String STREET_ALIAS_FILE = "prop/AAR_city_Con_StreetAlias.txt";
    private final String PATTERN_FILE = "prop/AAR_city_Con_Pattern.txt";
    private final String FORMAT_FILE = "prop/AAR_city_Con_Format.txt";//#1
    private final String EVENT_TYPE_EXTEND = "prop/EventTypeExtend.properties";
    //Property keys in HOU_IncCon.properties
    private final String PROP_KEY_DATA_SOURCE_URL = "DATA_SOURCE_URL";
    private final String PROP_KEY_SLEEP_TIME = "SLEEP_TIME";
    private final String PROP_KEY_RETRY_WAIT_TIME = "RETRY_WAIT_TIME";
    private final String PROP_KEY_TC_SEPARATE_SIGN = "TC_SEPARATE_SIGN";
    private final String PROP_KEY_REVERSE_GEOCODING_FLAG = "REVERSE_GEOCODING_FLAG";
    
    //log4j instance
    private static final Logger LOGGER = Logger.getLogger(AAR_city_Con.class);
    
    // int value 10 represents the inc/con/tta reader 
    private final int READER_TYPE = 10;
    
    // Reader ID
    private final String READER_ID = AAR_city_Con.class.getName();
    
    //save use memroy
    //private final String HOU_MEMORY_FILE="hou_memory.txt";
   
    //private 
    //private boolean flag=false;
    
    // TX state code
    private final String STATE = "MI";
    
    //HOU market code
    private final String MARKET = "AAR";
        
    // SimpleDateFormat to format the start time and end time 
    private final SimpleDateFormat DATE_FORMAT = new SimpleDateFormat(
			"MM dd, yyyy", Locale.US);
    private final SimpleDateFormat DATE_OTHER_FORMAT = new SimpleDateFormat(
			"MMM dd, yyyy", Locale.US);
    private static final SimpleDateFormat JAVADATEFORMAT_EXTEND = new SimpleDateFormat(
			"MMM dd, yyyy hh aa", Locale.US);
    //#3
    private static final SimpleDateFormat JAVADATEFORMAT_EXTEND1 = new SimpleDateFormat(
			"MMM dd, yyyy hh:mm aa", Locale.US);
    //end of #3
    //#5
	private static final SimpleDateFormat JAVADATEFORMAT_EXTEND2 = new SimpleDateFormat(
			"yyyy/MM/dd HH:mm:ss", Locale.US);
	private static final SimpleDateFormat JAVADATEFORMAT_EXTEND3 = new SimpleDateFormat(
			"yyyy/MM/dd hh aa", Locale.US);
	//end of #5
    private static final SimpleDateFormat JAVADATEFORMAT = new SimpleDateFormat(
			"MM dd, yyyy hh aa", Locale.US);
    //#8
	private static final SimpleDateFormat JAVADATEFORMAT_EXTEND4 = new SimpleDateFormat(
			"yyyy/MM/dd", Locale.US);
    //end of #8
	
    // TrafficCast Separate Sign
    private String tcSeparateSign = "~TrafficCastSeparateSign~";
    
    //If we need do reverse geocoding
    private boolean isReverseGeocoding = false;
    
    // sleep time, set default to 5 minutes, will load from property file
    private long loopSleepTime = 5 * 60 * 1000;

    // Retry wait time, set default to 2 minutes, will load from property file
    private long retryWaitTime = 2 * 60 * 1000;
    
    // General HOU Time Zone
    private TimeZone detTimeZone = null;
    
    // Address to get xml
    private String dataURL = "http://www.sccrc-roads.org/";
   
    // Matcher
  	private Matcher matcher = null;
    
    //ArrayList to store IncCon
    private ArrayList<IncConRecord> conArrayList = null;
    private ArrayList<IncConRecord> incArrayList = null;
    
    // Arraylist to store patterns
 	private ArrayList<Pattern> mainStPatternArrayList;
 	private ArrayList<Pattern> fromPatternArrayList;
 	private ArrayList<Pattern> toPatternArrayList;
 	
 	// key of pattern
 	private final String MAIN_ST_PATTERN = "MAIN_ST_PATTERN";
 	private final String FROM_PATTERN = "FROM_PATTERN";
 	private final String TO_PATTERN = "TO_PATTERN";
    
    // Hashmap to store street alias.
    private LinkedHashMap<String, String> streetAliasMap;
    
    // Map to store format
    private Map<String,List<Object>> formatMap;//#1
    private final String LOCATION_FORMAT = "LOCATION_FORMAT";//#1
    
    // This value is added to the wait time each time an exception is caught in run()
    private final int SEED = 60000;
    
    // for event type extend
 	private HashMap<String, String> eventTypeExtendMap;

    /**
     * Default constructor
     */
    private AAR_city_Con(){
    }//end of constructor
    
    /***
     * Main will create a new HOU_transtar_IncCon instance, call run function
     * @param args
     * @return none
     * @see
     */
    public static void main(String[] args) {
        PropertyConfigurator.configureAndWatch("log4j.properties", 60000);
        try {
        	AAR_city_Con incCon = new AAR_city_Con();
            incCon.run();
        } catch (Exception e) {
            LOGGER.fatal("Unexpected problem, program will terminate now(" + e.getMessage() +")");
        }
    }//end of main
    
    /**
     * Read xml from website,parse xml, analyze record, save to
     * database, Geocoding, sleep and then start another loop.
     * @param       None
     * @return      None
     * @exception   Exception
     * @see
     **/
    private void run() throws Exception
    {
		long startTime, sleepTime, waitTime = 0;

		// Only run when property file and road alias loaded and initialize OK.
		if (loadProperties() == true && loadStreetAlias() == true && loadPatterns() == true && loadFormat()
				&& loadEventTypeProperties() == true) {//#1
			LOGGER.info("Load properties and initialize completed, next will enter while()");
		} else {
			LOGGER.fatal(" properties failed ! Program will terminate");
			throw new RuntimeException(); // main() will catch this exception.
		}

		initVariables();
		while (true) {
			try {
				startTime = System.currentTimeMillis();
				LOGGER.info("Start to process Construction/Incident events");

				parseHtml();
				// Update data in DB.
				IncConDBUtils.updateDB(conArrayList, MARKET,
						EventType.CONSTRUCTION);
				IncConDBUtils.updateDB(incArrayList, MARKET,
						EventType.INCIDENT);

				// Update "last run" field in Mysql table containing reader
				// program IDs.
				DBUtils.updateReaderLastRun(loopSleepTime, READER_TYPE);

				// Geocoding.
				LOGGER.info("Starting GEOCoding process.");
				MySqlGeocodingEngine geo;
				geo = new MySqlGeocodingInitiater(MARKET, READER_ID);
				geo.initiateGeocoding();

				/**
				 * Sleep for an amount of time equal to either the difference
				 * between SLEEP_PERIOD and the running time of this iteration,
				 * or 1 second if this iteration took more than SLEEP_PERIOD
				 * milliseconds.
				 */
				conArrayList.clear();
				incArrayList.clear();
				System.gc();
				sleepTime = loopSleepTime
						- (System.currentTimeMillis() - startTime);
				if (sleepTime < 0) {
					sleepTime = 1000;
				}
                LOGGER.info("Last built on 11/11/2019; Ticket number:  #SD-1229");
				LOGGER.info("Sleeping for " + (sleepTime / 1000) + " seconds.");

				System.out.println();
				// Clean up.
				DBConnector.getInstance().disconnect();
				Thread.sleep(sleepTime);
				waitTime = 0;
			} catch (NoRouteToHostException ex) {
				LOGGER.warn("This machine's internet connection is unavailable, retrying in "
						+ retryWaitTime / 1000 + " seconds...");
				try {
					Thread.sleep(retryWaitTime);
				} catch (InterruptedException ex1) {
					LOGGER.fatal("Thread was interrupted.");
				}
			} catch (ConnectException ex) {
				LOGGER.warn("Connection was refused, retrying in "
						+ retryWaitTime / 1000 + " seconds...");
				try {
					Thread.sleep(retryWaitTime);
				} catch (InterruptedException ex1) {
					LOGGER.fatal("Thread was interrupted.");
				}
			} catch (UnknownHostException ex) {
				LOGGER.warn("Unkown host. Could not establish contact, retrying in "
						+ retryWaitTime / 1000 + " seconds...");
				try {
					Thread.sleep(retryWaitTime);
				} catch (InterruptedException ex1) {
					LOGGER.fatal("Thread was interrupted.");
				}
			} catch (FileNotFoundException ex) {
				LOGGER.warn("Could not retrieve data, retrying in "
						+ retryWaitTime / 1000 + " seconds...");
				try {
					Thread.sleep(retryWaitTime);
				} catch (InterruptedException ex1) {
					LOGGER.fatal("Thread was interrupted.");
				}
			} catch (IOException ex) {
				LOGGER.warn(ex.getMessage() + ", retrying in " + retryWaitTime
						/ 1000 + " seconds...");
				try {
					Thread.sleep(retryWaitTime);
				} catch (InterruptedException ex1) {
					LOGGER.fatal("Thread was interrupted.");
				}
			} catch (Exception ex) {
				waitTime += waitTime == 0 ? SEED : waitTime;
				LOGGER.log(Level.FATAL, "Unexpected exception (" + ex + "). "
						+ "Restarting parsing process in " + waitTime / 60000
						+ " minute(s).", ex);

				try {
					Thread.sleep(waitTime);
				} catch (InterruptedException ex1) {
					LOGGER.fatal("Thread interrupted!");
				}
			} finally {
				conArrayList.clear();
				incArrayList.clear();
			}
		} // end while
	} // end run()
    
    private void parseHtml() throws Exception {
		// DNS cache check
 		java.security.Security.setProperty("networkaddress.cache.negative.ttl",
				"0"); // unsuccessful DNS query cache
		java.security.Security.setProperty("networkaddress.cache.ttl", "0"); // successful
		System.setProperty("sun.net.inetaddr.ttl", "0");
		System.setProperty("sun.net.inetaddr.negative.ttl", "0");

		String line = null;
		BufferedReader reader = null;
		URLConnection con = null;
		URL detailurl = null;
		detailurl = new URL(dataURL);
		con = detailurl.openConnection();
		con.setConnectTimeout(120000);
		con.setReadTimeout(120000);
		reader = new BufferedReader(new InputStreamReader(con.getInputStream()));
		
		//reader = new BufferedReader(new FileReader("1.html"));
		
		String location = "";
		
		boolean start = false;
		
		while ((line = reader.readLine()) != null) {
			line = line.trim();			
			
			if (line.contains("City of Ann Arbor Construction ​an​d Traffic Controls​​​​")) {
				start = true;
				continue;
			}
									
			if (start && !line.contains("<div id=\"mdot\">")) {
				location += " " + line + " ";//#1
				continue;
			}
			
			if (line.contains("<div id=\"mdot\">")) {
				location += line.replace("<strong></strong>", "");
				location = location.replace("&#160;", " ").replace("&nbsp;", " ").replaceAll("<strong></strong>", "").replace("<strong> </strong>", "");
				//System.err.println(location);
				String[] records = location.split("<strong>");
			
				byte[] space = new byte[]{(byte) 0xE2,(byte) 0x80,(byte) 0x8B};    
				String UTFSpace = new String(space,"UTF-8");     
				for (int i = 1; i < records.length; i++) {					
					String record = records[i];
					record = record.replaceAll("<a href=\".*\">", "").replace("</a>", "");
					if (record.matches(".*</strong>.*the following streets? will .*")) {
						record =  records[i].split("</ul>")[0];
//						record = record.replaceAll("(.*&#58;.*)</strong>.*", "$1</strong>") + " " + records[i].split("</p><p>")[1] + " " + record.replaceAll("(.*&#58;.*)</strong>(.*)", "$2");
					}
					
					record = record.replaceAll(UTFSpace, " ");
					record = record.replace("&#160;", " ").replace("&nbsp;", " ").replace("&#58;", ":").replace("<br>", "").replace("</p>", "").replace("<strong> </strong>", "").replace("“", "\"").replace("—", "-").replace("–", "-").trim();
					record = record.replaceAll("\\bw ill\\b", "will").replaceAll("\\s+", " ");
					processRecord(record, detailurl);
				}
				break;
			}
		}		
	}
    
    private void processRecord(String lineInfo, URL detailurl) throws Exception {
		IncConRecord incConRecord = null;
		incConRecord = new IncConRecord();
		incConRecord.setState(STATE);
		incConRecord.setCity(MARKET);
		incConRecord.setMapUrl(detailurl);
		incConRecord.setTimeZone(detTimeZone);

		incConRecord.setType(EventType.CONSTRUCTION);		
		String mainSt = null;
		String startTime = null;
		String endTime = null;
		String description = null;
		String time = null;
		String mainFromTo = null;
		String fromSt = "";
		String toSt = "";
		TCTime startTCTime = null;
		TCTime endTCTime = null;
		String location = null;//#1
		String title = null;
		Boolean point = false;
		Boolean flag = false;
		String []items = null;
		IncConRecord incConRecordClone = null;
		//#2
//		if (lineInfo.matches(".*:(.*)</strong>.*")) {
//			time = lineInfo.replaceAll(".*:(.*)</strong>.*", "$1").trim().toUpperCase();
//		}
//		
//		if (lineInfo.matches(".*:.*</strong>(.*)")) {
//			description = lineInfo.replaceAll(".*:.*</strong>(.*)", "$1").toUpperCase();
//			title = lineInfo.replaceAll("(.*):.*</strong>(.*)", "$1").toUpperCase();
//		}
		//System.err.println(lineInfo);
		lineInfo = lineInfo.toUpperCase().replaceAll("(SOUTH|NORTH|WEST|EAST)BOU ND", "$1BOUND").replaceAll("(\\d+:) (\\d+ [A|P]\\.?M\\.?)", "$1$2");
		if (lineInfo.matches("(.*): (.*)</STRONG>(.*)")) {
			time = lineInfo.replaceAll("(.*): (.*)</STRONG>(.*)", "$2").trim();
			mainFromTo = lineInfo.replaceAll("(.*): (.*)</STRONG>(.*)", "$1").trim();
			description = lineInfo.replaceAll("(.*)</STRONG>(.*)", "$2").trim();
			title = lineInfo.replaceAll("(.*)</STRONG>(.*)", "$1").trim();
		}else{
			description = lineInfo.replaceAll("(.*)</STRONG>,?(.*)", "$2").trim();
			title = lineInfo.replaceAll("(.*)</STRONG>(.*)", "$1").trim();
			mainFromTo = lineInfo.replaceAll("(.*)</STRONG>(.*)", "$1").trim();
		}
	    //#4
		if(description == null|| description.equals("")){
		      return;
		 }
		//end of #4
//		title = formatLocation(title);
		location = description;//#1
		location = formatLocation(location);//#1
		String tmp = "";
	 if(time != null && !time.trim().equals("")){
			mainSt = processMainStreet(mainFromTo);
			fromSt = processCrossFrom(mainFromTo);
			toSt = processCrossTo(mainFromTo);
		if(title != null && !title.trim().equals("")){
			 if(title.matches("((.*)\\bFROM\\b(.*)\\bTO\\b(.*)):.*")){
				 tmp = title.replaceAll("((.*)\\bFROM\\b(.*)\\bTO\\b(.*)):.*", "$1");
				 items = tmp.split(";");
				 if(items.length > 0){
					mainSt = processMainStreet(items[0]);
					fromSt = processCrossFrom(items[0]);
					toSt = processCrossTo(items[0]);
				 }
			} //#6
			 else if(title.matches("((.*)\\bBETWEEN\\b(.*)\\bAND\\b(.*)):.*")){
				 tmp = title.replaceAll("((.*)\\bBETWEEN\\b(.*)\\bAND\\b(.*)):.*", "$1");
				 items = tmp.split(";");
				 if(items.length > 0){
					mainSt = processMainStreet(items[0]);
					fromSt = processCrossFrom(items[0]);
					toSt = processCrossTo(items[0]);
				 }
			}//end of #6
			 else if(title.matches(".*: \\w+DAY, \\w+\\.? \\d+ - TBA.*")){ //Pauline Blvd: Tuesday, May 1 - TBA.
				mainSt = title.replaceAll("(.*): \\w+DAY, \\w+\\.? \\d+ - TBA.*", "$1");
				fromSt = processCrossFrom(location);
				toSt = processCrossTo(location);
			}else if(title.matches(".*PROJECT: .*")){ //Crest, Buena Vista, W Washington Water Main Project: Tuesday Oct.2, 2018 - Saturday, Oct. 27 , 2018.
				location = location.replaceAll("(.*) WILL .*\\bBE CLOSED .*", "$1");
				items = location.split(",");
				if(items.length > 0){
				   mainSt = processMainStreet(items[0]);
				   fromSt = processCrossFrom(items[0]);
				   toSt = processCrossTo(items[0]);
				 }
			}
		}
		 if(mainSt == null ||"".equals(mainSt.trim()) || fromSt == null || "".equals(fromSt.trim())) {
			 mainSt = processMainStreet(location);
			 fromSt = processCrossFrom(location);
			 toSt = processCrossTo(location);
		 }
	}else{
		mainSt = processMainStreet(title);
		fromSt = processCrossFrom(title);
		toSt = processCrossTo(title);
		if(title != null && !title.trim().equals("")){
			if(title.matches(".*(\\d+ A.M. TO \\d+ P.M. (?:ON)?\\s*\\w+DAY, \\w+\\.? \\d+, \\d{4}).*")){ ///5 A.M. TO 12 P.M. ON THURSDAY, NOV. 22, 2018
				time = title.replaceAll(".*(\\d+ A.M. TO \\d+ P.M. (?:ON)?\\s*\\w+DAY, \\w+\\.? \\d+, \\d{4}).*", "$1");
			}else if(title.matches(".*\\w+DAY, \\w+\\.?\\s*\\d+, \\d+(?::\\d+)? (?:P.M.|A.M.) .*:.*")){ ///SATURDAY, NOV. 3, 3:45 P.M. GAME TIME:
				time = title.replaceAll(".*\\w+DAY, (\\w+\\.?\\s*\\d+), (\\d+(?::\\d+)? (?:P.M.|A.M.)) .*:.*", "$1 $2");
			}else if(title.matches(".*\\w+DAY, \\w+\\.?\\s*\\d+, \\d{4}: \\d+(?::\\d+)? (?:P.M.|A.M.) .*")){ ///SATURDAY, OCT. 26, 2019: 7: 30 P.M. UNIVERSITY OF MICHIGAN HOME FOOTBALL GAME :
				time = title.replaceAll(".*\\w+DAY, (\\w+\\.?\\s*\\d+, \\d{4}): (\\d+(?::\\d+)? (?:P.M.|A.M.)) .*", "$1 $2");
			}//#3
			else if(title.matches(".*\\w+DAY, \\w+\\.?\\s*\\d+, \\d{4} FROM \\d+(?::\\d+)?\\s*(?:TO|-)\\s*\\d+(?::\\d+)? (?:P.M.|A.M.).*")){ //Sunday, March 10, 2019 from 8 to 11 a.m.
				time = title.replaceAll(".*\\w+DAY, (\\w+\\.?\\s*\\d+, \\d{4} FROM \\d+(?::\\d+)?\\s*(?:TO|-)\\s*\\d+(?::\\d+)? (?:P.M.|A.M.)).*", "$1");
			}//end of #3
			else if(title.matches("\\d+ (?:P.M.|A.M.) - NOON ON \\w+DAY, \\w+\\.?\\s*\\d+, \\d{4}.*")){
				time = title.replaceAll("(\\d+ (?:P.M.|A.M.) - NOON ON \\w+DAY, \\w+\\.?\\s*\\d+, \\d{4}).*", "$1");
			}else if(title.matches("\\d+ (?:P.M.|A.M.) (?:ON\\s)?\\w+DAY, \\w+\\.?\\s*\\d+ THROUGH \\d+ (?:P.M.|A.M.) (?:ON\\s)?\\w+DAY, \\w+\\.?\\s*\\d+.*")){//7 a.m. Tuesday, Oct. 23 through 4 a.m. on Wednesday, Oct. 24,
				time = title.replaceAll("(\\d+ (?:P.M.|A.M.) (?:ON\\s)?\\w+DAY, \\w+\\.?\\s*\\d+ THROUGH \\d+ (?:P.M.|A.M.) (?:ON\\s)?\\w+DAY, \\w+\\.?\\s*\\d+).*", "$1");
			}
			
			//#5
			if(time == null || "".equals(time)){
				time = title.toUpperCase().trim();
			}

		    if(mainSt == null ||"".equals(mainSt.trim()) || fromSt == null || "".equals(fromSt.trim())) {
				mainSt = processMainStreet(location);
				fromSt = processCrossFrom(location);
				toSt = processCrossTo(location);
			}
			//end of #5
		}
	}	
	   //#5
       if(location != null && !location.equals("") && location.matches(".*<LI>(.*)</LI>.*")){
    	   items = location.replaceAll(".*<UL><LI>(.*)</LI>", "$1").split("</LI><LI>");
    	   if(items.length > 0){
    		   if(processMainStreet(items[0]) == null ||"".equals(processMainStreet(items[0]).trim()) 
    				   || processCrossFrom(items[0]) == null || "".equals(processCrossFrom(items[0]).trim())){
					  flag = true;
				  }
    		   if(flag == false){
    			  mainSt = processMainStreet(items[0]);
  				  fromSt = processCrossFrom(items[0]);
  				  toSt = processCrossTo(items[0]);
    		   }
    		   point = true;
		   } 
       }
       //end of #5

		//end of #2
		if (!"".equals(mainSt) && mainSt != null) {
			if (!getDir(mainSt).equals("")) {
				incConRecord.setMain_dir(getDir(mainSt));
			}
			incConRecord.setMain_st(formatStreet(mainSt));
		}
		
		//#5
		if(incConRecord.getMain_dir() == null || "".equals(incConRecord.getMain_dir())){
			if(!"".equals(getDir(location))){
				incConRecord.setMain_dir(getDir(location));
			}
		}
		//end of #5
		if (incConRecord.getMain_dir() == null && description.matches(".* IN THE (WEST|EAST|SOUTH|NORTH)BOUND DIRECTION.*")) {
			incConRecord.setMain_dir(getDir(description.replaceAll(".* IN THE (WEST|EAST|SOUTH|NORTH)BOUND DIRECTION.*", "$1BOUND")));
		} else if (incConRecord.getMain_dir() == null && description.matches(".*RESTRICT .* (WEST|EAST|SOUTH|NORTH)BOUND .*")) {
			incConRecord.setMain_dir(getDir(description.replaceAll(".*RESTRICT .* (WEST|EAST|SOUTH|NORTH)BOUND .*", "$1BOUND")));
		}
		
		if (!"".equals(fromSt) && !"".equals(formatStreet(fromSt))) {
			incConRecord.setFrom_st(formatStreet(fromSt));
		} 
		
		if (!"".equals(toSt) && !"".equals(formatStreet(toSt))) {
			incConRecord.setTo_st(formatStreet(toSt));
		}
		
		Calendar calendar = Calendar.getInstance(detTimeZone, Locale.US);
	if(time != null && !time.trim().equals("")){
		//#6
		time = time.replaceAll("\\bNOON\\b", "12:00 PM").replaceAll("\\bMID-?NIGHT\\b", "11:59 PM");
		//end of #6
		time = time.replace("A.M.", "AM").replace("P.M.", "PM").replaceAll("([A|P])\\.M\\.?", "$1M");
		//#5
		if (time.matches(".*\\d+ AM\\s*(?:TO|-)\\s*\\d+ PM,? (?:ON)?\\s*\\w+DAY, \\w+\\.? \\d+\\s*-\\s*\\w+DAY, \\w+\\.? \\d+, \\d{4}.*")) {//9 AM-3 PM, MONDAY, APRIL 8-MONDAY, APRIL 15, 2019.
			startTime = time.replaceAll(".*(\\d+ AM)\\s*(?:TO|-)\\s*\\d+ PM,? (?:ON)?\\s*\\w+DAY, (\\w+\\.? \\d+)\\s*-\\s*\\w+DAY, \\w+\\.? \\d+, (\\d{4}).*", "$2"+", "+"$3 $1").replace(".", "").trim();
			endTime = time.replaceAll(".*\\d+ AM\\s*(?:TO|-)\\s*(\\d+ PM),? (?:ON)?\\s*\\w+DAY, \\w+\\.? \\d+\\s*-\\s*\\w+DAY, (\\w+\\.? \\d+, \\d{4}).*", "$2 $1").replace(".", "").trim();
			startTime = startTime.replace("SEPT ", "SEP ");
			endTime = endTime.replace("SEPT ", "SEP ");
		
			if(JAVADATEFORMAT_EXTEND.parse(startTime).before(JAVADATEFORMAT_EXTEND2.parse(getCurrentTime()))
					&& JAVADATEFORMAT_EXTEND.parse(endTime).after(JAVADATEFORMAT_EXTEND2.parse(getCurrentTime()))){
				startTime = getLocaleDate() + time.replaceAll(".*(\\d+ AM)\\s*(?:TO|-)\\s*\\d+ PM,? (?:ON)?\\s*\\w+DAY, \\w+\\.? \\d+\\s*-\\s*\\w+DAY, \\w+\\.? \\d+, \\d{4}.*", " $1");
				endTime = getLocaleDate() + time.replaceAll(".*\\d+ AM\\s*(?:TO|-)\\s*(\\d+ PM),? (?:ON)?\\s*\\w+DAY, \\w+\\.? \\d+\\s*-\\s*\\w+DAY, \\w+\\.? \\d+, \\d{4}.*", " $1");
				if(JAVADATEFORMAT_EXTEND3.parse(startTime).before(JAVADATEFORMAT_EXTEND2.parse(getCurrentTime()))
						&& JAVADATEFORMAT_EXTEND3.parse(endTime).after(JAVADATEFORMAT_EXTEND2.parse(getCurrentTime()))){
					startTCTime = new TCTime(JAVADATEFORMAT_EXTEND3, startTime, detTimeZone);
					endTCTime = new TCTime(JAVADATEFORMAT_EXTEND3, endTime, detTimeZone);
					//#8
					if(startTCTime != null){
						incConRecord.setStartTime(startTCTime);
					}
					if(endTCTime != null){
						incConRecord.setEndTime(endTCTime);
					}
					//end of #8
				}else{
					return;
				}
			}else{
				return;
			}
		} //#5
		else if (time.matches(".*\\d+ AM\\s*(?:TO|-)\\s*\\d+ PM (?:ON)?\\s*\\w+DAY, \\w+\\.? \\d+, \\d{4}.*")) {//7 AM TO 8 PM SATURDAY, OCT. 20, 2018. ///5 AM TO 12 PM ON THURSDAY, NOV. 22, 2018
			startTime = time.replaceAll(".*(\\d+ AM)\\s*(?:TO|-)\\s*(\\d+ PM) (?:ON)?\\s*\\w+DAY, (\\w+\\.? \\d+, \\d+{4}).*", "$3 $1").replace(".", "").trim();
			endTime = time.replaceAll(".*(\\d+ AM)\\s*(?:TO|-)\\s*(\\d+ PM) (?:ON)?\\s*\\w+DAY, (\\w+\\.? \\d+, \\d+{4}).*", "$3 $2").replace(".", "").trim();
			startTime = startTime.replace("SEPT ", "SEP ");
			endTime = endTime.replace("SEPT ", "SEP ");
			startTCTime = new TCTime(JAVADATEFORMAT_EXTEND, startTime, detTimeZone);
			endTCTime = new TCTime(JAVADATEFORMAT_EXTEND, endTime, detTimeZone);
			//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			if(endTCTime != null){
				incConRecord.setEndTime(endTCTime);
			}
			//end of #8
		} else if (time.matches("(?:\\w+DAY,\\s)?\\w+\\.? \\d+, \\d+{4}-TB[AD].*")) {// June 23, 2017-TBD 
			startTime = time.replaceAll("(?:\\w+DAY,\\s)?(\\w+\\.? \\d+, \\d+{4})-TB[AD].*", "$1").replace(".", "").trim();
			startTime = startTime.replace("SEPT ", "SEP ");
			startTCTime = new TCTime(DATE_OTHER_FORMAT, startTime, detTimeZone);
			//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			//end of #8
		} else if (time.matches(".*\\w+DAY,? \\w+\\.?\\s*\\d+(?:, \\d{4})?\\s*-\\s*\\w+DAY, \\w+\\.?\\s*\\d+.*\\d{4}.*")) {//MONDAY, OCT. 22-TUESDAY, OCT. 30​, 2018.// TUESDAY OCT.2, 2018 - SATURDAY, OCT. 27 , 2018. ///MONDAY, OCT. 29 - MONDAY, NOV. 5, 2018.  
			startTime = time.replaceAll(".*\\w+DAY,? (\\w+\\.?\\s*\\d+)(?:, \\d{4})?\\s*-\\s*\\w+DAY, (\\w+\\.?\\s*\\d+).*(\\d{4}).*", "$1, "+calendar.get(Calendar.YEAR)).replace(".", " ").replaceAll("\\s+", " ").trim();
			if(time.matches(".*\\w+DAY,? \\w+\\.?\\s*\\d+, \\d{4}\\s*-\\s*\\w+DAY, \\w+\\.?\\s*\\d+.*\\d{4}.*")){
				startTime = time.replaceAll(".*\\w+DAY,? (\\w+\\.?\\s*\\d+, \\d{4})\\s*-\\s*\\w+DAY, (\\w+\\.?\\s*\\d+).*(\\d{4}).*", "$1").replace(".", " ").replaceAll("\\s+", " ").trim();
			}
			String year = time.replaceAll(".*\\w+DAY,? (\\w+\\.?\\s*\\d+)(?:, \\d{4})?\\s*-\\s*\\w+DAY, (\\w+\\.?\\s*\\d+).*(\\d{4}).*", "$3");
			String month = time.replaceAll(".*\\w+DAY,? (\\w+\\.?\\s*\\d+)(?:, \\d{4})?\\s*-\\s*\\w+DAY, (\\w+)\\.?\\s*(\\d+).*(\\d{4}).*", "$2");
			String day = time.replaceAll(".*\\w+DAY,? (\\w+\\.?\\s*\\d+)(?:, \\d{4})?\\s*-\\s*\\w+DAY, (\\w+)\\.?\\s*(\\d+).*(\\d{4}).*", "$3");
			startTime = startTime.replace("SEPT ", "SEP ");
			startTCTime = new TCTime(DATE_OTHER_FORMAT, startTime, detTimeZone);
			endTime = month + " " + day + ", " + year;
			endTime = endTime.replace("SEPT ", "SEP ");
			endTCTime = new TCTime(DATE_OTHER_FORMAT, endTime, detTimeZone);
			//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			if(endTCTime != null){
				incConRecord.setEndTime(endTCTime);
			}
			//end of #8
		} else if (time.matches(".*\\w+DAY, \\w+\\.? \\d+-\\w+\\.? \\d+, \\d+{4}.*")) {//Monday, June 19-July 14, 2017
			startTime = time.replaceAll(".*\\w+DAY, (\\w+\\.? \\d+)-(\\w+\\.? \\d+), (\\d+{4}).*", "$1, $3").replace(".", "").trim();
			endTime = time.replaceAll(".*\\w+DAY, (\\w+\\.? \\d+)-(\\w+\\.? \\d+), (\\d+{4}).*", "$2, $3").replace(".", "").trim();
			
			startTime = startTime.replace("SEPT ", "SEP ");
			endTime = endTime.replace("SEPT ", "SEP ");
			startTCTime = new TCTime(DATE_OTHER_FORMAT, startTime, detTimeZone);
			endTCTime = new TCTime(DATE_OTHER_FORMAT, endTime, detTimeZone);
			//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			if(endTCTime != null){
				incConRecord.setEndTime(endTCTime);
			}
			//end of #8
		}//#6 
		else if (time.matches(".*\\w+DAY, \\w+\\.? \\d+\\s*-\\s*\\w+DAY, \\w+\\.? \\d+.*")) {//MONDAY, APRIL 29-FRIDAY, MAY 17 .
			startTime = time.replaceAll(".*\\w+DAY, (\\w+\\.? \\d+)\\s*-\\s*\\w+DAY, (\\w+\\.? \\d+).*", "$1").replace(".", "").trim()+", "+getLocaleYear();
			endTime = time.replaceAll(".*\\w+DAY, (\\w+\\.? \\d+)\\s*-\\s*\\w+DAY, (\\w+\\.? \\d+).*", "$2").replace(".", "").trim()+", "+getLocaleYear();
			startTime = startTime.replace("SEPT ", "SEP ");
			endTime = endTime.replace("SEPT ", "SEP ");
			
			startTCTime = new TCTime(DATE_OTHER_FORMAT, startTime, detTimeZone);
			endTCTime = new TCTime(DATE_OTHER_FORMAT, endTime, detTimeZone);
			//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			if(endTCTime != null){
				incConRecord.setEndTime(endTCTime);
			}
			//end of #8
		}//end of #6
		else if (time.matches("\\w+\\.? \\d+-\\w+\\.? \\d+, \\d+{4}.*")) {//June 19-SEPT ember 1, 2017
			startTime = time.replaceAll("(\\w+\\.? \\d+)-(\\w+\\.? \\d+), (\\d+{4}).*", "$1, $3").replace(".", "").trim();
			endTime = time.replaceAll("(\\w+\\.? \\d+)-(\\w+\\.? \\d+), (\\d+{4}).*", "$2, $3").replace(".", "").trim();
			startTime = startTime.replace("SEPT ", "SEP ");
			endTime = endTime.replace("SEPT ", "SEP ");
			
			startTCTime = new TCTime(DATE_OTHER_FORMAT, startTime, detTimeZone);
			endTCTime = new TCTime(DATE_OTHER_FORMAT, endTime, detTimeZone);
			//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			if(endTCTime != null){
				incConRecord.setEndTime(endTCTime);
			}
			//end of #8
		} else if (time.matches("(?:\\w+DAY,\\s)?\\w+\\.? \\d+\\s*-\\s*\\w+\\.?,? \\d+{4}.*")) {//Monday, May 1-August 2017
			startTime = time.replaceAll("(?:\\w+DAY,\\s)?(\\w+\\.? \\d+)\\s*-\\s*(\\w+\\.?),? (\\d+{4}).*", "$1, $3").replace(".", "").trim();
			endTime = time.replaceAll("(?:\\w+DAY,\\s)?(\\w+\\.? \\d+)\\s*-\\s*(\\w+\\.?),? (\\d+{4}).*", "$2 1, $3").replace(".", "").trim();
			startTime = startTime.replace("SEPT ", "SEP ");
			endTime = endTime.replace("SEPT ", "SEP ");
			
			startTCTime = new TCTime(DATE_OTHER_FORMAT, startTime, detTimeZone);
			endTCTime = new TCTime(DATE_OTHER_FORMAT, endTime, detTimeZone);
			//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			if(endTCTime != null){
				incConRecord.setEndTime(endTCTime);
			}
			//end of #8
		} else if (time.matches("(?:\\w+DAY,\\s)?\\w+\\.? \\d+, \\d+{4} UNTIL .*")) {//Monday, May 15, 2017 until further notice.
			startTime = time.replaceAll("(?:\\w+DAY,\\s)?(\\w+\\.? \\d+, \\d+{4}) UNTIL .*", "$1").replace(".", "").trim();
			startTime = startTime.replace("SEPT ", "SEP ");
			
			startTCTime = new TCTime(DATE_OTHER_FORMAT, startTime, detTimeZone);
			//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			//end of #8
		} else if (time.matches("(?:\\w+DAY,\\s)?\\w+\\.? \\d+(?:,\\sAPPROXIMATELY\\s\\d+\\s(?:PM|AM))?\\s*-\\s*TB[AD].*")) {//Saturday, June 17-TBA. ///TUESDAY, MAY 1 - TBA.////FRIDAY, NOV. 9, APPROXIMATELY 4 PM-TBD.
			Calendar cal = Calendar.getInstance(detTimeZone, Locale.US);
			startTime = time.replaceAll("(?:\\w+DAY,\\s)?(\\w+\\.? \\d+)(?:,\\sAPPROXIMATELY\\s\\d+\\s(?:PM|AM))?\\s*-\\s*TB[AD].*", "$1, ".replace(".", "") + cal.get(Calendar.YEAR)).replace(".", "").trim();
			startTime = startTime.replace("SEPT ", "SEP ");
			startTCTime = new TCTime(DATE_OTHER_FORMAT, startTime, detTimeZone);
			if(time.matches("(?:\\w+DAY,\\s)?\\w+\\.? \\d+,\\sAPPROXIMATELY\\s\\d+\\s(?:PM|AM)\\s*-\\s*TB[AD].*")){
				startTime = startTime + time.replaceAll("(?:\\w+DAY,\\s)?\\w+\\.? \\d+,\\sAPPROXIMATELY\\s(\\d+\\s(?:PM|AM))\\s*-\\s*TB[AD].*", " $1");
				startTCTime = new TCTime(JAVADATEFORMAT_EXTEND, startTime, detTimeZone);
			}
			//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			//end of #8
		}//#5
		else if(time.matches("\\d+ [A|P]M,? \\w+DAY,? \\w+\\.? \\d+(?:, \\d{4})?\\s*-\\s*\\d+ [A|P]M,? \\w+DAY,? \\w+\\.? \\d+\\s*,? \\d{4}.*")){//9 a.m., Monday Feb. 4-5 p.m., Friday, April 12​, 2019 (closure extended).
			if(time.matches("\\d+ [A|P]M,? \\w+DAY,? \\w+\\.? \\d+, \\d{4}\\s*-\\s*\\d+ [A|P]M,? \\w+DAY,? \\w+\\.? \\d+\\s*,? \\d{4}.*")){
				startTime = time.replaceAll("(\\d+ [A|P]M),? \\w+DAY,? (\\w+\\.? \\d+, \\d{4})\\s*-\\s*\\d+ [A|P]M,? \\w+DAY,? \\w+\\.? \\d+\\s*,? \\d{4}.*", "$2 $1");
				startTime = startTime.replace("SEPT ", "SEP ");
				startTCTime = new TCTime(JAVADATEFORMAT_EXTEND, startTime, detTimeZone);
			}
			if(time.matches("\\d+ [A|P]M,? \\w+DAY,? \\w+\\.? \\d+\\s*-\\s*\\d+ [A|P]M,? \\w+DAY,? \\w+\\.? \\d+\\s*,? \\d{4}.*")){
				startTime = time.replaceAll("(\\d+ [A|P]M),? \\w+DAY,? (\\w+\\.? \\d+)\\s*-\\s*\\d+ [A|P]M,? \\w+DAY,? \\w+\\.? \\d+\\s*,? (\\d{4}).*", "$2, $3 $1").replace(".", "");
				startTime = startTime.replace("SEPT ", "SEP ");
				startTCTime = new TCTime(JAVADATEFORMAT_EXTEND, startTime.replace("SEPT ", "SEP "), detTimeZone);
			}
			endTime = time.replaceAll("\\d+ [A|P]M,? \\w+DAY,? \\w+\\.? \\d+(?:, \\d{4})?\\s*-\\s*(\\d+ [A|P]M),? \\w+DAY,? (\\w+\\.? \\d+)\\s*,? (\\d{4}).*", "$2, $3 $1").replace(".", "");
			endTime = endTime.replace("SEPT ", "SEP ");
			endTCTime = new TCTime(JAVADATEFORMAT_EXTEND, endTime.replace("SEPT ", "SEP "), detTimeZone);
			//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			if(endTCTime != null){
				incConRecord.setEndTime(endTCTime);
			}
			//end of #8
		}else if(time.matches("\\d+ [A|P]M \\w+DAY,? \\w+\\.? \\d+\\s*-\\s*\\d+ [A|P]M")
				&& location.matches("\\w+DAY,? \\w+\\.? \\d+,? \\d{4}.*")){//9 a.m. Monday, April 1-5 p.m.<Strong>Friday, April 5, 2019(It's special because part of the time is lost)
			startTime = time.replaceAll("(\\d+ [A|P]M) \\w+DAY,? (\\w+\\.? \\d+)\\s*-\\s*\\d+ [A|P]M", "$2, "+getLocaleYear()+" $1").replace(".", "");
			endTime = location.replaceAll("\\w+DAY,? (\\w+\\.? \\d+,? \\d{4}).*", "$1").replace(".", "") + " " + time.replaceAll("\\d+ AM \\w+DAY,? \\w+\\.? \\d+\\s*-\\s*(\\d+ PM)", "$1");
			startTime = startTime.replace("SEPT ", "SEP ");
			endTime = endTime.replace("SEPT ", "SEP ");
			startTCTime = new TCTime(JAVADATEFORMAT_EXTEND, startTime, detTimeZone);
			endTCTime = new TCTime(JAVADATEFORMAT_EXTEND, endTime, detTimeZone);
			//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			if(endTCTime != null){
				incConRecord.setEndTime(endTCTime);
			}
			//end of #8
		}
//		else if(time.matches("\\w+DAY,? \\w+\\.? \\d+,? \\d{4},? NOON\\s*-\\s*MIDNIGHT")){//Friday, April 5, 2019, noon-midnight
//			startTime = time.replaceAll("\\w+DAY,? (\\w+\\.? \\d+),? (\\d{4}),? NOON\\s*-\\s*MIDNIGHT", "$1, $2").replace(".", "") + " 12:00 PM";
//			endTime = time.replaceAll("\\w+DAY,? (\\w+\\.? \\d+),? (\\d{4}),? NOON\\s*-\\s*MIDNIGHT", "$1, $2").replace(".", "") + " 11:59 PM";
//			startTCTime = new TCTime(JAVADATEFORMAT_EXTEND1, startTime, detTimeZone);
//			incConRecord.setStartTime(startTCTime);
//			endTCTime = new TCTime(JAVADATEFORMAT_EXTEND1, endTime, detTimeZone);
//			incConRecord.setEndTime(endTCTime);
//		}
		//FRIDAY, SEPT . 6, 2019 FROM 5 AM - 11 PM
		else if(time.matches("\\w+DAY,? \\w+\\.? \\d+,? \\d{4},?(?:\\sFROM)? \\d+(?::\\d+)? [A|P]M\\s*-\\s*\\d+(?::\\d+)? [A|P]M,?")){//Saturday, April 6, 2019, 8 a.m.-8 p.m.
			startTime = time.replaceAll("\\w+DAY,? (\\w+\\.? \\d+),? (\\d{4}),?(?:\\sFROM)? (\\d+(?::\\d+)? [A|P]M)\\s*-\\s*\\d+(?::\\d+)? [A|P]M,?", ", $2 $3").replace(".", "");
			String month = time.replaceAll("\\w+DAY,? (\\w+)\\.? (\\d+),? (\\d{4}),?(?:\\sFROM)? (\\d+(?::\\d+)? [A|P]M)\\s*-\\s*\\d+(?::\\d+)? [A|P]M,?", "$1").replace(".", "");
			endTime = time.replaceAll("\\w+DAY,? (\\w+\\.? \\d+),? (\\d{4}),?(?:\\sFROM)? \\d+(?::\\d+)? [A|P]M\\s*-\\s*(\\d+(?::\\d+)? [A|P]M),?", ", $2 $3").replace(".", "");
			String day = time.replaceAll("\\w+DAY,? (\\w+)\\.? (\\d+),? (\\d{4}),?(?:\\sFROM)? \\d+(?::\\d+)? [A|P]M\\s*-\\s*(\\d+(?::\\d+)? [A|P]M),?", "$2").replace(".", "");
			if (month != null && month.length() > 3) {
            	month = month.substring(0, 3);
			}
            startTime = month + " " + day + startTime;
            endTime = month + " " + day + endTime;
			if(startTime.matches("\\w+ \\d+, \\d{4} \\d+:\\d+ [A|P]M")){
            	startTCTime = new TCTime(JAVADATEFORMAT_EXTEND1, startTime, detTimeZone);
            }else if(startTime.matches("\\w+ \\d+, \\d{4} \\d+ [A|P]M")){
            	startTCTime = new TCTime(JAVADATEFORMAT_EXTEND, startTime, detTimeZone);
            }
            if(endTime.matches("\\w+ \\d+, \\d{4} \\d+:\\d+ [A|P]M")){
            	endTCTime = new TCTime(JAVADATEFORMAT_EXTEND1, endTime, detTimeZone);
            }else if(endTime.matches("\\w+ \\d+, \\d{4} \\d+ [A|P]M")){
            	endTCTime = new TCTime(JAVADATEFORMAT_EXTEND, endTime, detTimeZone);
            }
           
        	//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			if(endTCTime != null){
				incConRecord.setEndTime(endTCTime);
			}
			//end of #8
		}else if(time.matches("\\w+DAY,? \\w+\\.? \\d+,? \\d{4},? \\d+(?::\\d+)?\\s*-\\s*\\d+(?::\\d+)? [A|P]M")){//SUNDAY, APRIL 7, 2019, 5:30-10:30 AM 
			startTime = time.replaceAll("\\w+DAY,? (\\w+\\.? \\d+),? (\\d{4}),? (\\d+(?::\\d+)?)\\s*-\\s*\\d+(?::\\d+)? ([A|P]M)", "$1, $2 $3 $4").replace(".", "");
			endTime = time.replaceAll("\\w+DAY,? (\\w+\\.? \\d+),? (\\d{4}),? \\d+(?::\\d+)?\\s*-\\s*(\\d+(?::\\d+)? [A|P]M)", "$1, $2 $3").replace(".", "");
			startTime = startTime.replace("SEPT ", "SEP ");
			endTime = endTime.replace("SEPT ", "SEP ");
            if(startTime.matches("\\w+ \\d+, \\d{4} \\d+:\\d+ [A|P]M")){
            	startTCTime = new TCTime(JAVADATEFORMAT_EXTEND1, startTime, detTimeZone);
            }else if(startTime.matches("\\w+ \\d+, \\d{4} \\d+ [A|P]M")){
            	startTCTime = new TCTime(JAVADATEFORMAT_EXTEND, startTime, detTimeZone);
            }
            if(endTime.matches("\\w+ \\d+, \\d{4} \\d+:\\d+ [A|P]M")){
            	endTCTime = new TCTime(JAVADATEFORMAT_EXTEND1, endTime, detTimeZone);
            }else if(startTime.matches("\\w+ \\d+, \\d{4} \\d+ [A|P]M")){
            	endTCTime = new TCTime(JAVADATEFORMAT_EXTEND, endTime, detTimeZone);
            }
    
        	//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			if(endTCTime != null){
				incConRecord.setEndTime(endTCTime);
			}
			//end of #8
		}//end of #5
		else if(time.matches("\\d+(?::\\d+)? [P|A]M,? \\w+DAY,? \\w+\\.?\\s*\\d+.*\\w+DAY, \\w+\\.?\\s*\\d+, \\d{4}.*")){///9 AM TUESDAY, OCT. 30–FRIDAY, NOV. 16, 2018​.//9 AM, MONDAY FEB. 4-5 PM SATURDAY, FEB. 23, 2019.
			startTime = time.replaceAll("(\\d+(?::\\d+)? [P|A]M),? \\w+DAY,? (\\w+\\.?\\s*\\d+).*\\w+DAY, \\w+\\.?\\s*\\d+, (\\d{4}).*", "$2, $3 $1").replace(".", " ").replaceAll("\\s+", " ").trim();
			//#6
			//#3
			startTime = startTime.replace("SEPT ", "SEP ");
			if(time.matches("\\d+(?::\\d+)? [P|A]M,? \\w+DAY,? \\w+\\.?\\s*\\d+\\s*-\\s*\\d+(?::\\d+)? [P|A]M \\w+DAY, \\w+\\.?\\s*\\d+, \\d{4}.*")){
				endTime = time.replaceAll("\\d+(?::\\d+)? [P|A]M,? \\w+DAY,? \\w+\\.?\\s*\\d+\\s*-\\s*(\\d+(?::\\d+)? [P|A]M) \\w+DAY, (\\w+\\.?\\s*\\d+, \\d{4}).*", "$2 $1").replace(".", " ").replaceAll("\\s+", " ").trim();
				endTime = endTime.replace("SEPT ", "SEP ");
				if(!endTime.contains(":")){
					endTime = endTime.trim().replaceAll("(\\w+\\.?\\s*\\d+, \\d{4}) (\\d+) ([P|A]M)", "$1 $2" + ":00 $3");
				}
				endTCTime = new TCTime(JAVADATEFORMAT_EXTEND1, endTime, detTimeZone);
			}else if(time.matches("\\d+(?::\\d+)? [P|A]M,? \\w+DAY,? \\w+\\.?\\s*\\d+.*\\w+DAY, (\\w+\\.?\\s*\\d+, \\d{4}).*")){
				endTime = time.replaceAll("\\d+(?::\\d+)? [P|A]M,? \\w+DAY,? \\w+\\.?\\s*\\d+.*\\w+DAY, (\\w+\\.?\\s*\\d+, \\d{4}).*", "$1").replace(".", " ").replaceAll("\\s+", " ").trim();
				endTCTime = new TCTime(DATE_OTHER_FORMAT, endTime.replace("SEPT ", "SEP "), detTimeZone);
			}
			//end of #3
			if(!startTime.contains(":")){
				startTime = startTime.trim().replaceAll("(\\w+\\.?\\s*\\d+, \\d{4}) (\\d+) ([P|A]M)", "$1 $2" + ":00 $3");
			}
			startTCTime = new TCTime(JAVADATEFORMAT_EXTEND1, startTime.replace("SEPT ", "SEP "), detTimeZone); 
			//end of #6
			//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			if(endTCTime != null){
				incConRecord.setEndTime(endTCTime);
			}
			//end of #8
		}else if(time.matches(".*THE WEEK OF \\w+\\.? \\d+.*")){ ///THE WEEK OF OCTOBER 8
			startTime = time.replaceAll(".*THE WEEK OF (\\w+\\.? \\d+).*", "$1, "+calendar.get(Calendar.YEAR)).replace(".", "").trim();
			startTime = startTime.replace("SEPT ", "SEP ");
			startTCTime = new TCTime(DATE_OTHER_FORMAT, startTime, detTimeZone);
			//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			//end of #8
		}else if(time.matches("\\w+DAY, \\w+\\.?\\s*\\d+, \\d+ (?:AM|PM).*")){ ///Saturday, Nov. 17, 4 p.m. 
			startTime = time.replaceAll("\\w+DAY, (\\w+\\.?\\s*\\d+), \\d+ (?:AM|PM).*", "$1").replace(".", " ").replaceAll("\\s+", " ").trim() + ", " + calendar.get(Calendar.YEAR)
					     + time.replaceAll("\\w+DAY, \\w+\\.?\\s*\\d+, (\\d+ (?:AM|PM)).*", " $1").trim();
			startTime = startTime.replace("SEPT ", "SEP ");
			startTCTime = new TCTime(JAVADATEFORMAT_EXTEND, startTime, detTimeZone);
			//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			//end of #8
			
		}//#3
		else if(time.matches("(?:\\w+DAY)?,?\\s*\\w+\\.?\\s*\\d+, \\d{4} FROM \\d+(?::\\d+)?\\s*(?:TO|-)\\s*\\d+(?::\\d+)? (?:AM|PM).*")){ //Sunday, March 10, 2019 from 8 to 11 a.m.//APRIL 7, 2019 FROM 5:30 TO 10:30 AM
			startTime = time.replaceAll("(?:\\w+DAY)?,?\\s*(\\w+\\.?\\s*\\d+, \\d{4}) FROM \\d+(?::\\d+)?\\s*(?:TO|-)\\s*\\d+(?::\\d+)? (?:AM|PM).*", "$1").replace(".", " ").replaceAll("\\s+", " ").trim() + " "
					     + time.replaceAll("(?:\\w+DAY)?,?\\s*\\w+\\.?\\s*\\d+, \\d{4} FROM (\\d+(?::\\d+)?)\\s*(?:TO|-)\\s*\\d+(?::\\d+)? (AM|PM).*", " $1 $2").trim();
			endTime = time.replaceAll("(?:\\w+DAY)?,?\\s*(\\w+\\.?\\s*\\d+, \\d{4}) FROM \\d+(?::\\d+)?\\s*(?:TO|-)\\s*\\d+(?::\\d+)? (?:AM|PM).*", "$1").replace(".", " ").replaceAll("\\s+", " ").trim() + " "
				     + time.replaceAll("(?:\\w+DAY)?,?\\s*\\w+\\.?\\s*\\d+, \\d{4} FROM \\d+(?::\\d+)?\\s*(?:TO|-)\\s*(\\d+(?::\\d+)?) (AM|PM).*", " $1 $2").trim();
			startTime = startTime.replace("SEPT ", "SEP ");
			endTime = endTime.replace("SEPT ", "SEP ");
			if(time.matches("(?:\\w+DAY)?,?\\s*\\w+\\.?\\s*\\d+, \\d{4} FROM \\d+:\\d+\\s*(?:TO|-)\\s*\\d+:\\d+ (?:AM|PM).*")){
				startTCTime = new TCTime(JAVADATEFORMAT_EXTEND1, startTime, detTimeZone);
				endTCTime = new TCTime(JAVADATEFORMAT_EXTEND1, endTime, detTimeZone);
			}else if(time.matches("(?:\\w+DAY)?,?\\s*\\w+\\.?\\s*\\d+, \\d{4} FROM \\d+\\s*(?:TO|-)\\s*\\d+ (?:AM|PM).*")){
				startTCTime = new TCTime(JAVADATEFORMAT_EXTEND, startTime, detTimeZone);
				endTCTime = new TCTime(JAVADATEFORMAT_EXTEND, endTime, detTimeZone);
			}else if(time.matches("(?:\\w+DAY)?,?\\s*\\w+\\.?\\s*\\d+, \\d{4} FROM \\d+\\s*(?:TO|-)\\s*\\d+:\\d+ (?:AM|PM).*")){
				startTCTime = new TCTime(JAVADATEFORMAT_EXTEND, startTime, detTimeZone);
				endTCTime = new TCTime(JAVADATEFORMAT_EXTEND1, endTime, detTimeZone);
			}else if(time.matches("(?:\\w+DAY)?,?\\s*\\w+\\.?\\s*\\d+, \\d{4} FROM \\d+:\\d+\\s*(?:TO|-)\\s*\\d+ (?:AM|PM).*")){
				startTCTime = new TCTime(JAVADATEFORMAT_EXTEND1, startTime, detTimeZone);
				endTCTime = new TCTime(JAVADATEFORMAT_EXTEND, endTime, detTimeZone);
			}
			
			if(startTCTime.getDate().after(endTCTime.getDate())||startTCTime.getDate().compareTo(endTCTime.getDate()) == 0){
				startTCTime.add(-12 * 60 * 60 * 1000);
			}
			//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			if(endTCTime != null){
				incConRecord.setEndTime(endTCTime);
			}
			//end of #8
		}//end of #3
		else if(time.matches("\\w+DAY,? \\w+\\.?\\s*\\d+ AND \\w+DAY,? \\w+\\.?\\s*\\d+ FROM \\d+(?::\\d+)?\\s*(AM|PM)(?:TO|-)\\s*\\d+(?::\\d+)?\\s*(AM|PM).*")){ //THURSDAY, JULY 25 AND THURSDAY, AUG. 22 FROM 6 AM-3 PM
			String year = getLocaleYear();
			startTime = time.replaceAll("\\w+DAY,? (\\w+)\\.?\\s*(\\d+) AND \\w+DAY,? (\\w+)\\.?\\s*(\\d+) FROM (\\d+(?::\\d+))?\\s*(AM|PM)(?:TO|-)\\s*(\\d+(?::\\d+)?)\\s*(AM|PM).*", "$1 $2") + ", " + year + 
					time.replaceAll("\\w+DAY,? (\\w+)\\.?\\s*(\\d+) AND \\w+DAY,? (\\w+)\\.?\\s*(\\d+) FROM (\\d+(?::\\d+))?\\s*(AM|PM)(?:TO|-)\\s*(\\d+(?::\\d+)?)\\s*(AM|PM).*", " $1 $2");
			endTime = time.replaceAll("(?:\\w+DAY)?,?\\s*(\\w+\\.?\\s*\\d+, \\d{4}) FROM \\d+(?::\\d+)?\\s*(?:TO|-)\\s*\\d+(?::\\d+)? (?:AM|PM).*", "$1").replace(".", " ").replaceAll("\\s+", " ").trim() + " "
				     + time.replaceAll("(?:\\w+DAY)?,?\\s*\\w+\\.?\\s*\\d+, \\d{4} FROM \\d+(?::\\d+)?\\s*(?:TO|-)\\s*(\\d+(?::\\d+)?) (AM|PM).*", " $1 $2").trim();
			startTime = startTime.replace("SEPT ", "SEP ");
			endTime = endTime.replace("SEPT ", "SEP ");
			if(time.matches("(?:\\w+DAY)?,?\\s*\\w+\\.?\\s*\\d+, \\d{4} FROM \\d+:\\d+\\s*(?:TO|-)\\s*\\d+:\\d+ (?:AM|PM).*")){
				startTCTime = new TCTime(JAVADATEFORMAT_EXTEND1, startTime, detTimeZone);
				endTCTime = new TCTime(JAVADATEFORMAT_EXTEND1, endTime, detTimeZone);
			}else if(time.matches("(?:\\w+DAY)?,?\\s*\\w+\\.?\\s*\\d+, \\d{4} FROM \\d+\\s*(?:TO|-)\\s*\\d+ (?:AM|PM).*")){
				startTCTime = new TCTime(JAVADATEFORMAT_EXTEND, startTime, detTimeZone);
				endTCTime = new TCTime(JAVADATEFORMAT_EXTEND, endTime, detTimeZone);
			}else if(time.matches("(?:\\w+DAY)?,?\\s*\\w+\\.?\\s*\\d+, \\d{4} FROM \\d+\\s*(?:TO|-)\\s*\\d+:\\d+ (?:AM|PM).*")){
				startTCTime = new TCTime(JAVADATEFORMAT_EXTEND, startTime, detTimeZone);
				endTCTime = new TCTime(JAVADATEFORMAT_EXTEND1, endTime, detTimeZone);
			}else if(time.matches("(?:\\w+DAY)?,?\\s*\\w+\\.?\\s*\\d+, \\d{4} FROM \\d+:\\d+\\s*(?:TO|-)\\s*\\d+ (?:AM|PM).*")){
				startTCTime = new TCTime(JAVADATEFORMAT_EXTEND1, startTime, detTimeZone);
				endTCTime = new TCTime(JAVADATEFORMAT_EXTEND, endTime, detTimeZone);
			}
			
			if(startTCTime.getDate().after(endTCTime.getDate())||startTCTime.getDate().compareTo(endTCTime.getDate()) == 0){
				startTCTime.add(-12 * 60 * 60 * 1000);
			}
			//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			if(endTCTime != null){
				incConRecord.setEndTime(endTCTime);
			}
			//end of #8
		}
		else if(time.matches("\\d+ (?:AM|PM),? (?:ON\\s)?\\w+DAY,? \\w+\\.?\\s*\\d+\\s*(?:THROUGH|TO|-)\\s*\\d+ (?:PM|AM) (?:ON\\s)?\\w+DAY,? \\w+\\.?\\s*\\d+,?\\s*(?:\\d{4})?.*")){//7 a.m. Tuesday, Oct. 23 through 4 a.m. on Wednesday, Oct. 24, //9 AM, MONDAY FEB. 4-5 PM FRIDAY MARCH 8, 2019
			startTime = time.replaceAll("\\d+ (?:AM|PM),? (?:ON\\s)?\\w+DAY,? (\\w+\\.?\\s*\\d+)\\s*(?:THROUGH|TO|-)\\s*\\d+ (?:PM|AM) (?:ON\\s)?\\w+DAY,? \\w+\\.?\\s*\\d+,?\\s*(?:\\d{4})?.*", "$1, ").replace(".", " ").replaceAll("\\s+", " ")+calendar.get(Calendar.YEAR)
					     + time.replaceAll("(\\d+ (?:AM|PM)),? (?:ON\\s)?\\w+DAY,? \\w+\\.?\\s*\\d+\\s*(?:THROUGH|TO|-)\\s*\\d+ (?:PM|AM) (?:ON\\s)?\\w+DAY,? \\w+\\.?\\s*\\d+,?\\s*(?:\\d{4})?.*"," $1");
			endTime = time.replaceAll("\\d+ (?:AM|PM),? (?:ON\\s)?\\w+DAY,? \\w+\\.?\\s*\\d+\\s*(?:THROUGH|TO|-)\\s*\\d+ (?:PM|AM) (?:ON\\s)?\\w+DAY,? (\\w+\\.?\\s*\\d+),?\\s*(?:\\d{4})?.*", "$1, ").replace(".", " ").replaceAll("\\s+", " ")+calendar.get(Calendar.YEAR)
			          + time.replaceAll("\\d+ (?:AM|PM),? (?:ON\\s)?\\w+DAY,? \\w+\\.?\\s*\\d+\\s*(?:THROUGH|TO|-)\\s*(\\d+ (?:PM|AM)) (?:ON\\s)?\\w+DAY,? \\w+\\.?\\s*\\d+,?\\s*(?:\\d{4})?.*"," $1");
			startTime = startTime.replace("SEPT ", "SEP ");
			endTime = endTime.replace("SEPT ", "SEP ");
			startTCTime = new TCTime(JAVADATEFORMAT_EXTEND, startTime, detTimeZone);
			endTCTime = new TCTime(JAVADATEFORMAT_EXTEND, endTime, detTimeZone);
			//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			if(endTCTime != null){
				incConRecord.setEndTime(endTCTime);
			}
			//end of #8
		}else if(time.matches("\\d+ (?:AM|PM) - NOON ON \\w+DAY, \\w+\\.?\\s*\\d+, \\d{4}.*")){////5 a.m. - noon on Thursday, Nov. 22, 2018
			startTime = time.replaceAll("(\\d+ (?:AM|PM)) - NOON ON \\w+DAY, (\\w+\\.?\\s*\\d+), (\\d{4}).*", "$2, $3 $1").replace(".", " ").replaceAll("\\s+", " ").trim(); 
			endTime = time.replaceAll("\\d+ (?:AM|PM) - NOON ON \\w+DAY, (\\w+\\.?\\s*\\d+), (\\d{4}).*", "$1, $2" + " 12 PM").replace(".", " ").replaceAll("\\s+", " ").trim(); 
			startTime = startTime.replace("SEPT ", "SEP ");
			endTime = endTime.replace("SEPT ", "SEP ");
			
			startTCTime = new TCTime(JAVADATEFORMAT_EXTEND, startTime, detTimeZone);
			endTCTime = new TCTime(JAVADATEFORMAT_EXTEND, endTime, detTimeZone);
			//#8
			if(startTCTime != null){
				incConRecord.setStartTime(startTCTime);
			}
			if(endTCTime != null){
				incConRecord.setEndTime(endTCTime);
			}
			//end of #8
		}else if(time.matches(".*CONCLUDE IN (?:JANUARY|FEBRUARY|MARCH|APRIL|MAY|JUNE|JULY|AUGUST|SEPTEMBER|OCTOBER|NOVEMBER|DECEMBER),? \\d{4}.*")){// to conclude in June, 2019. 
			endTime = time.replaceAll(".*CONCLUDE IN (JANUARY|FEBRUARY|MARCH|APRIL|MAY|JUNE|JULY|AUGUST|SEPTEMBER|OCTOBER|NOVEMBER|DECEMBER),? (\\d{4}).*", "$1 1, $2");
			endTCTime = new TCTime(DATE_OTHER_FORMAT, endTime, detTimeZone);
			//#8
			if(endTCTime != null){
				incConRecord.setEndTime(endTCTime);
			}
		}else if(time.matches(".*\\d+(?::\\d+) [AP]M .* FOOTBALL GAME :.*")){
			if(title != null && title.matches(".*\\w+DAY, \\w+\\.? \\d+, \\d{4}: \\d+(?::\\d+) [AP]\\.?M\\.? .* FOOTBALL GAME :.*")){
				startTime = title.replaceAll(".*\\w+DAY, (\\w+)\\.? (\\d+, \\d{4}): \\d+(?::\\d+) [AP]\\.?M\\.? .* FOOTBALL GAME :.*", "$1 $2");
				startTCTime = new TCTime(DATE_OTHER_FORMAT, startTime, detTimeZone);
				if(startTCTime != null){
					incConRecord.setStartTime(startTCTime);
				}
				if(incConRecord.getStartTime().getDate().before(JAVADATEFORMAT_EXTEND4.parse(getLocaleDate()))){
					return;
				}
			}
		}
		//end of #8
	}	
	
		description = new String(description.getBytes("utf-8"),"iso8859-1");
		description = description.replaceAll("Â", "");
		description = new String(description.getBytes("iso8859-1"), "UTF-8");
		description = description.replaceAll("�", "");
		description = description.replaceAll("<SPAN .*?>", "");
		description = description.replaceAll("<A.*?>(.*)</A>", "");
		description = description.replaceAll("&AMP;", "&");
		description = description.replaceAll("&QUOT;", "\"");
		description = description.replaceAll("\\s\\s+", " ");
		description = description.replaceAll("<P.*?>", "");
//		description = description.replaceAll("</?[a-zA-Z]+[^><]*>", "").trim();
		
		if (description.contains("DAYTIME") || description.contains("DAILY")) {
			if (description.matches(".* FROM \\d A.M. TO \\d P.M..*")) {
				Calendar currentCal = Calendar.getInstance(detTimeZone, Locale.US);
				String currentDate = (currentCal.get(Calendar.MONTH) + 1) + " "
						+ currentCal.get(Calendar.DAY_OF_MONTH) + ", "
						+ currentCal.get(Calendar.YEAR);
				TCTime currentTCTime = new TCTime(DATE_FORMAT,
						currentDate, detTimeZone);
				if (currentTCTime.compareTo(incConRecord.getStartTime()) >= 0) {
					startTime = currentDate + " " + description.replaceAll(".* FROM (\\d) A.M. TO (\\d) P.M..*", "$1 AM");
					endTime = currentDate + " " + description.replaceAll(".* FROM (\\d) A.M. TO (\\d) P.M..*", "$2 PM");
					startTCTime = new TCTime(JAVADATEFORMAT, startTime, detTimeZone);
					endTCTime = new TCTime(JAVADATEFORMAT, endTime, detTimeZone);
					//#8
					if(startTCTime != null){
						incConRecord.setStartTime(startTCTime);
					}
					if(endTCTime != null){
						incConRecord.setEndTime(endTCTime);
					}
					//end of #8
				}
			}
		}

		//#8
		if(description != null && description.matches(".*\\bPLEASE VISIT.*")){
			description = description.replaceAll("(.*)\\bPLEASE VISIT.*", "$1").trim();
		}
		//end of #8
		if(description.startsWith(".")){
			description = description.replaceAll("\\.(.*)", "$1").trim();
		}
		if(description.length() > 1000){
            description = description.substring(0, 1000);
            description = description.substring(0, description.lastIndexOf(".") + 1);
        }
		//#2
		description = description.replaceAll("\\s+", " ").trim();
		//end of #2
		if (!description.replaceAll("</?[a-zA-Z]+[^><]*>", "").trim().endsWith(".")) {
			description = description + ".";
		}
		incConRecord.setDescription(description.replaceAll("</?[a-zA-Z]+[^><]*>", "").trim().toUpperCase());
		//#2
		incConRecord.setChecked(99);
		incConRecord.setUnreliable(2);
		
		//#5
		if(location.matches(".*(?:NORTH|SOUTH|WEST|EAST)BOUND TRAFFIC ON .* FROM .* TO .*(?:NORTH|SOUTH|WEST|EAST)BOUND TRAFFIC .* FROM .* TO .*")){
			String main_dir = location.replaceAll(".*(?:NORTH|SOUTH|WEST|EAST)BOUND TRAFFIC ON .* FROM .* TO .*((?:NORTH|SOUTH|WEST|EAST)BOUND) TRAFFIC .* FROM .* TO .*", "$1");
			main_dir = getDir(main_dir);
			fromSt = location.replaceAll(".*(?:NORTH|SOUTH|WEST|EAST)BOUND TRAFFIC ON .* FROM .* TO .*(?:NORTH|SOUTH|WEST|EAST)BOUND TRAFFIC .* FROM (.*) TO .*", "$1");
			toSt = location.replaceAll(".*(?:NORTH|SOUTH|WEST|EAST)BOUND TRAFFIC ON .* FROM .* TO .*(?:NORTH|SOUTH|WEST|EAST)BOUND TRAFFIC .* FROM .* TO (.*)", "$1");
			incConRecordClone = incConRecord.clone();
			//#6
			if(!"".equals(main_dir)){
				incConRecordClone.setMain_dir(main_dir);
			}
			incConRecordClone.setFrom_st(formatStreet(fromSt));
            if(!"".equals(getDir(fromSt))){
            	incConRecordClone.setFrom_dir(getDir(fromSt));
			}
			incConRecordClone.setTo_st(formatStreet(toSt));
			if(!"".equals(getDir(toSt))){
				incConRecordClone.setTo_dir(getDir(toSt));
			}
			//end of #6
			if(incConRecordClone.getMain_st() != null && !"".equals(incConRecordClone.getMain_st())){
				if(incConRecordClone.getMain_st().equals(fromSt)){
					if(!fromSt.equals(toSt)){
						incConRecordClone.setFrom_st(toSt);
						//#6
						if(!"".equals(getDir(toSt))){
							incConRecordClone.setFrom_dir(getDir(toSt));
						}
						//end of #6
						incConRecordClone.setTo_st(null);
						incConRecordClone.setTo_dir(null);
					}else{
						incConRecordClone.setTo_st(null);
						incConRecordClone.setTo_dir(null);
					}
				}else{
					if(fromSt != null && fromSt.equals(toSt)){
						incConRecordClone.setTo_st(null);
						incConRecordClone.setTo_dir(null);
					}
				}
				
			}
			if (incConRecord.getType().equals(EventType.INCIDENT)) {
				incArrayList.add(incConRecordClone);
			} else if (incConRecord.getType().equals(EventType.CONSTRUCTION)) {
				conArrayList.add(incConRecordClone);
			}
		}
		//end of #5
		
		//#6
		if(items == null && description.matches(".*<UL><LI>(.*)</LI>.*")){
			items = description.replaceAll(".*<UL><LI>(.*)</LI>", "$1").split("</LI><LI>");
		}
		//end of #6
		String des = "";
		if(items != null && items.length > 0){
			incConRecordClone = incConRecord.clone();
			for(String item : items){
				if(point){
					//#5
					if(item != null && !"".equals(item)){
						item = item.replace("&AMP;", "&").replace("&#160;", " ").replace("&NBSP;", " ").replace("&#58;", ":").replace("&QUOT;", "\"");
						item = item.replaceAll("</?[a-zA-Z]+[^><]*>", "");
						if(item.toUpperCase().trim().endsWith(".")){
							//#6
							if(!item.endsWith("A.M.") && !item.endsWith("P.M.")){
								item = item.replaceAll("(.*)\\.", "$1");
							}
							//end of #6
						}
					}
					//end of #5
					if(flag == false){
						des = item.toUpperCase() + " WILL BE CLOSED FOR SPECIAL EVENT.";
						des = des.replaceAll("\\s+", " ");
						if(!des.trim().endsWith(".")){
							 des = des + ".";
						 }
						incConRecordClone.setDescription(des);
					}
				} 
				// extend description key
				String descr = incConRecordClone.getDescription();
				String key = "";
				Iterator<String> iteratorDesc1 = eventTypeExtendMap.keySet().iterator();
				while (iteratorDesc1.hasNext()) {
					key = iteratorDesc1.next();
					if (descr.toUpperCase().contains(key.toString())) {
						if (eventTypeExtendMap.get(key).equals("1")) {
							incConRecordClone.setType(EventType.INCIDENT);
						} else if (eventTypeExtendMap.get(key).equals("2")) {
							incConRecordClone.setType(EventType.CONSTRUCTION);
						}
					}
				}
				//#6
				des = des.replaceAll("\\bNOON\\b", "12:00 PM");
				if(des != null && des.matches(".*\\bFROM \\d+(?::\\d+)? [A|P]\\.?M\\.? ON \\w+DAY, \\w+\\.? \\d+ UNTIL \\d+(?::\\d+)? [A|P]\\.?M\\.? ON \\w+DAY, \\w+ \\d+, \\d{4}.*")){//from 4 p.m. on Saturday, June 2 until 2 p.m. on Sunday, June 2, 2019
					des = des.replaceAll("(A|P)\\.?M\\.?", "$1M");
					startTime = des.replaceAll(".*\\bFROM (\\d+(?::\\d+)? [A|P]M) ON \\w+DAY, (\\w+\\.? \\d+) UNTIL \\d+(?::\\d+)? [A|P]M ON \\w+DAY, \\w+ \\d+, (\\d{4}).*", "$2, $3 $1");
					endTime = des.replaceAll(".*\\bFROM \\d+(?::\\d+)? [A|P]M ON \\w+DAY, \\w+\\.? \\d+ UNTIL (\\d+(?::\\d+)? [A|P]M) ON \\w+DAY, (\\w+ \\d+, \\d{4}).*", "$2 $1");
					if(!startTime.contains(":")){
						startTime = startTime.replaceAll("(\\w+ \\d+, \\d{4} \\d+) ([A|P]M)", "$1" + ":00 $2");
					}
					incConRecordClone.setStartTime(new TCTime(JAVADATEFORMAT_EXTEND1, startTime, detTimeZone));
					if(!endTime.contains(":")){
						endTime = endTime.replaceAll("(\\w+ \\d+, \\d{4} \\d+) ([A|P]M)", "$1" + ":00 $2");
					}
					incConRecordClone.setEndTime(new TCTime(JAVADATEFORMAT_EXTEND1, endTime, detTimeZone));
				}else if(des != null && des.matches(".*\\bFROM \\d+(?::\\d+)? [A|P]\\.?M\\.? TO \\d+(?::\\d+)? [A|P]\\.?M\\.?.*")){
					des = des.replaceAll("(A|P)\\.?M\\.?", "$1M");
					if(time != null && time.matches("\\w+DAY, \\w+ \\d+, \\d{4}")){
						startTime = time.replaceAll("\\w+DAY, (\\w+ \\d+, \\d{4})", "$1 ") + des.replaceAll(".*\\bFROM (\\d+(?::\\d+)? [A|P]M) TO \\d+(?::\\d+)? [A|P]M\\b.*", "$1");
						if(!startTime.contains(":")){
							startTime = startTime.replaceAll("(\\w+ \\d+, \\d{4} \\d+) ([A|P]M)", "$1" + ":00 $2");
						}
						incConRecordClone.setStartTime(new TCTime(JAVADATEFORMAT_EXTEND1, startTime, detTimeZone));
						endTime = time.replaceAll("\\w+DAY, (\\w+ \\d+, \\d{4})", "$1 ") + des.replaceAll(".*\\bFROM \\d+(?::\\d+)? [A|P]M TO (\\d+(?::\\d+)? [A|P]M)\\b.*", "$1");
						if(!endTime.contains(":")){
							endTime = endTime.replaceAll("(\\w+ \\d+, \\d{4} \\d+) ([A|P]M)", "$1" + ":00 $2");
						}
						incConRecordClone.setEndTime(new TCTime(JAVADATEFORMAT_EXTEND1, endTime, detTimeZone));
					}
				}
				item = item.replaceAll("(?:FROM|BETWEEN) (?:\\d+(?::\\d+)? [A|P]\\.?M\\.?) (?:TO|AND) (\\d+(?::\\d+)? [A|P]\\.?M\\.?).*", "");
				item = item.replaceAll("(?:FROM|BETWEEN) NOON (?:TO|AND) (\\d+(?::\\d+)? [A|P]\\.?M\\.?).*", "");
				item = item.replaceAll("(?:FROM|BETWEEN) (?:\\d+(?::\\d+)? [A|P]\\.?M\\.?) (?:TO|AND) NOON\\b.*", "");
				item = item.replaceAll("FROM (?:\\d+(?::\\d+)? [A|P]\\.?M\\.?).*", "");
				//end of #6 
				//#8
				if(point){
					if(flag == false){
						incConRecordClone.setMain_st(formatStreet(processMainStreet(formatLocation(item.toUpperCase()))));
						incConRecordClone.setFrom_st(formatStreet(processCrossFrom(formatLocation(item.toUpperCase()))));
						incConRecordClone.setTo_st(formatStreet(processCrossTo(formatLocation(item.toUpperCase()))));
					}
				}else{
					incConRecordClone.setMain_st(formatStreet(processMainStreet(formatLocation(item.toUpperCase()))));
					incConRecordClone.setFrom_st(formatStreet(processCrossFrom(formatLocation(item.toUpperCase()))));
					incConRecordClone.setTo_st(formatStreet(processCrossTo(formatLocation(item.toUpperCase()))));
				}
				//end of #8
				
				if (incConRecordClone.getType().equals(EventType.INCIDENT)) {
					incArrayList.add(incConRecordClone);
				} else if (incConRecordClone.getType().equals(EventType.CONSTRUCTION)) {
					conArrayList.add(incConRecordClone);
				}
				incConRecordClone = incConRecord.clone();
			}
		}else{
			if (incConRecord.getType().equals(EventType.INCIDENT)) {
				incArrayList.add(incConRecord);
			} else if (incConRecord.getType().equals(EventType.CONSTRUCTION)) {
				conArrayList.add(incConRecord);
			}
		}
		
    	//end of #2
	}
    
    //#5
	public String getCurrentTime() throws ParseException {
		Calendar cal = Calendar.getInstance();
		cal.setTimeZone(detTimeZone);
		int year = cal.get(Calendar.YEAR);
		int month = cal.get(Calendar.MONTH) + 1;
		int day = cal.get(Calendar.DAY_OF_MONTH);
		int hour = cal.get(Calendar.HOUR_OF_DAY);
		int minutes = cal.get(Calendar.MINUTE);
		int seconds = cal.get(Calendar.SECOND);

		String date = String.valueOf(year) + "/" + String.valueOf(month) + "/"
				+ String.valueOf(day) + " " + String.valueOf(hour) + ":"
				+ String.valueOf(minutes) + ":" + String.valueOf(seconds);
		return date;
	}
	
	public String getLocaleDate() {
		Calendar cal = Calendar.getInstance();
		cal.setTimeZone(TimeZone.getTimeZone("US/Eastern"));
		int year = cal.get(Calendar.YEAR);
		int month = cal.get(Calendar.MONTH) + 1;
		int day = cal.get(Calendar.DAY_OF_MONTH);
		String date = String.valueOf(year) + "/" + String.valueOf(month) + "/"
				+ String.valueOf(day);
		return date;
	}
	
	public String getLocaleYear() {
		Calendar cal = Calendar.getInstance();
		cal.setTimeZone(detTimeZone);
		int year = cal.get(Calendar.YEAR);
		String date = String.valueOf(year);
		return date;
	}
	//end of #5
	
	/**
	 * Process main street
	 * 
	 * @param location
	 *            location from xml element.
	 * @return standard road name
	 * @exception Exception
	 * @see
	 */
	private String processMainStreet(String location) throws Exception {
		String mainStreet = "";
		if (location == null) {
			LOGGER.info("location is null, processMainSt returns null.");
			return null;
		}

		for (Pattern pattern : mainStPatternArrayList) {
			if ((matcher = pattern.matcher(location)).find()) {
				mainStreet = matcher.group(1);

				LOGGER.debug("MainSt:" + mainStreet);
				break;
			}
		}

		return mainStreet;
	} // End of processMainStreet.

	/**
	 * Use Regex to parse cross_from in location, this information is from
	 * Headline of xml record.
	 * 
	 * @param location
	 *            headLine of xml record which contains cross_from
	 * @return String standard road name
	 * @exception
	 * @see
	 */
	private String processCrossFrom(String location) {
		String fromSt = "";

		if (location == null) {
			LOGGER.info("location is null, processCrossFrom returns null.");
			return fromSt;
		}

		for (Pattern pattern : fromPatternArrayList) {
			if ((matcher = pattern.matcher(location)).find()) {
				fromSt = matcher.group(1);
				LOGGER.debug("CrossFrom:" + fromSt);//#1
				fromSt = formatStreet(fromSt);
				break;
			}
		}
		return fromSt;
	} // end of processCrossFrom

	/**
	 * Use Regex to parse cross_to in location, this information is from
	 * Headline of xml record.
	 * 
	 * @param location
	 *            headLine of xml record which contains cross_to
	 * @return String Standard road name
	 * @exception
	 * @see
	 */
	private String processCrossTo(String location) {
		String toSt = "";
		if (location == null) {
			LOGGER.info("location is null, processCrossto returns null.");
			return null;
		}

		for (Pattern pattern : toPatternArrayList) {
			if ((matcher = pattern.matcher(location)).find()) {
				toSt = matcher.group(1);
				LOGGER.debug("CrossTo:" + toSt);//#1
				toSt = formatStreet(toSt);		
				break;
			}
		}
		return toSt;
	} // end of processCrossTo
    
    public String getDir(String main_info) {
		if (main_info.matches(".*(SOUTHBOUND|SB) .*") || main_info.equals("SOUTHBOUND")) {
			return "SB";
		}
		if (main_info.matches(".*(NORTHBOUND|NB) .*") || main_info.equals("NORTHBOUND")) {
			return "NB";
		}
		if (main_info.matches(".*(EASTBOUND|EB) .*") || main_info.equals("EASTBOUND")) {
			return "EB";
		}
		if (main_info.matches(".*(WESTBOUND|WB) .*") || main_info.equals("WESTBOUND")) {
			return "WB";
		}		
		return "";
	}

	/**
	 * Use Regex to parse the street name of MainSt or CrossFrom or CrossTo
	 * 
	 * @param street
	 * @return The standard street
	 * @see
	 */
	private String formatStreet(String street) {
		String key = "", value = "";
		Iterator<String> iterator = streetAliasMap.keySet().iterator();
		while (iterator.hasNext()) {
			key = iterator.next();
			street = street.trim();
			value = streetAliasMap.get(key);
			street = street.replaceAll(key, value);
		}
		LOGGER.debug("End of formatStreet:" + street);
		return street;
	} // end of formatStreet

	/**
	 * Initianize instance level variables
	 * 
	 * @param None
	 * @return None.
	 * @exception
	 * @see
	 */
	private void initVariables() throws Exception {
		// Initialize ArrayList which store IncConRecord and Hashmap store
		// unknown error
		conArrayList = new ArrayList<IncConRecord>();
		incArrayList = new ArrayList<IncConRecord>();
		/**
		 * Use "HOU" to get timezone. This is okay since TX state only has one
		 * timezone, Central time.
		 */
		DBConnector.getInstance().setReaderID(READER_ID);
		detTimeZone = DBUtils.getTimeZone(MARKET, STATE);
		//#3
		DATE_FORMAT.setTimeZone(detTimeZone);
		DATE_OTHER_FORMAT.setTimeZone(detTimeZone);
		JAVADATEFORMAT_EXTEND.setTimeZone(detTimeZone);
		JAVADATEFORMAT_EXTEND1.setTimeZone(detTimeZone);
		JAVADATEFORMAT_EXTEND2.setTimeZone(detTimeZone);
		JAVADATEFORMAT_EXTEND3.setTimeZone(detTimeZone);
		JAVADATEFORMAT.setTimeZone(detTimeZone);
		//end of #3
		LOGGER.info("initVariable successfully");
	} // End of initVariables.

	/**
	 * Load property file,get url,sleep time if there is any exception,program
	 * will terminate,program will run ok only when all properties edit
	 * successfully;
	 * 
	 * @param None
	 * @return true if all properties successfully,otherwise return false.
	 * @exception
	 * @see
	 */
	private boolean loadProperties() {
		String propValue;
		Properties prop = new Properties();
		FileInputStream is = null;
		LOGGER.info("Start to load properties file");
		try {
			is = new FileInputStream(PROPERTY_FILE);
			prop.load(is);
						
			// Get Incident url
			propValue = prop.getProperty(PROP_KEY_DATA_SOURCE_URL);
			if (propValue != null) {
				dataURL = propValue.trim();
			}
			LOGGER.info("dataURL :" + dataURL);

			// Sleep time is optional,if there is no such value,use default 5
			// minutes
			propValue = prop.getProperty(PROP_KEY_SLEEP_TIME);
			if (propValue != null && propValue.length() > 0) {
				loopSleepTime = Long.parseLong(propValue);
			}
			LOGGER.info("loopSleep time: " + loopSleepTime);

			// Retry wait time,optional,default is 2 minutes
			propValue = prop.getProperty(PROP_KEY_RETRY_WAIT_TIME);
			if (propValue != null && propValue.length() > 0) {
				retryWaitTime = Long.parseLong(propValue);
			}
			LOGGER.info("Retry wait time:" + retryWaitTime);

			// If we need do reverse geocoding,default is false
			propValue = prop.getProperty(PROP_KEY_REVERSE_GEOCODING_FLAG);
			if (propValue != null && propValue.length() > 0) {
				isReverseGeocoding = Boolean.valueOf(propValue);
			}
			LOGGER.info("if do reverse geocoding:" + isReverseGeocoding);

			/**
			 * TrafficCast separate sign, optional, default is
			 * "[TrafficCastSeparateSign]" At least 5 characters
			 */
			propValue = prop.getProperty(PROP_KEY_TC_SEPARATE_SIGN);
			if (propValue != null && propValue.length() >= 5) {
				tcSeparateSign = propValue;
			}
			LOGGER.info("tcSeparateSign:" + tcSeparateSign);

			LOGGER.info("Properties loaded successfully");
			return true;
		} catch (FileNotFoundException ex) {
			LOGGER.fatal("Properties file:" + PROPERTY_FILE
					+ "does not exit,program will terminate now ("
					+ ex.getMessage() + ")");
			return false;
		} catch (IOException ex) {
			LOGGER.fatal("Parse properties error,program will terminate now("
					+ ex.getMessage() + ")");
			return false;
		} finally {
			try {
				if (is != null) {
					is.close();
				}
			} catch (IOException e) {
				is = null;
			}
		}
	} // end of loadProperties
	/**
	 * Load Street alias file, will be used to format Road
	 * 
	 * @param None
	 * @return true if loaded successfully, otherwise return false.
	 * @exception
	 * @see
	 */
	private boolean loadStreetAlias() {
		BufferedReader buffReader = null;
		String lineRead;
		String[] keyValue;

		streetAliasMap = new LinkedHashMap<String, String>();
		LOGGER.info("Start to load street alias");

		try {
			buffReader = new BufferedReader(new FileReader(STREET_ALIAS_FILE));

			while ((lineRead = buffReader.readLine()) != null) {
				if (lineRead.length() < tcSeparateSign.length() + 2
						|| lineRead.startsWith("#")) {
					LOGGER.info("Empty or comment line, skipped:" + lineRead);
					continue;
				}
				keyValue = lineRead.split(tcSeparateSign);

				if (keyValue != null && keyValue.length > 1) {
					LOGGER.info("STREET ALIAS: " + keyValue[0] + " = "
							+ keyValue[1]);
					streetAliasMap.put(keyValue[0], keyValue[1]);
				}
			} // End of while

			LOGGER.info("Load street alias successfully");
			return true;
		} catch (FileNotFoundException ex) {
			LOGGER.fatal("Street alias file:" + STREET_ALIAS_FILE
					+ " does not exist, program will terminate now ("
					+ ex.getMessage() + ")");
			return false;
		} catch (Exception ex) {
			LOGGER.fatal("Parse street alias error, program will terminate now ("
					+ ex.getMessage() + ")");
			return false;
		} finally {
			try {
				if (buffReader != null) {
					buffReader.close();
				}
			} catch (IOException e) {
				buffReader = null;
			}
		}
	} // End of loadStreetAlias()
	
	/**
	 * Load patterns, used in search main_st, cross_from, cross_to
	 * 
	 * @param None
	 * @return true if loaded successfully, otherwise return false.
	 * @exception
	 * @see
	 */
	private boolean loadPatterns() {
		String lineRead;
		String[] keyValue;
		Pattern pattern;
		BufferedReader buffReader = null;

		mainStPatternArrayList = new ArrayList<Pattern>();
		fromPatternArrayList = new ArrayList<Pattern>();
		toPatternArrayList = new ArrayList<Pattern>();
		LOGGER.info("Start to load patterns");

		try {
			buffReader = new BufferedReader(new FileReader(PATTERN_FILE));

			while ((lineRead = buffReader.readLine()) != null) {
				if (lineRead.length() < tcSeparateSign.length() + 2
						|| lineRead.startsWith("#")) {
					LOGGER.info("Empty or comment line, skipped:" + lineRead);
					continue;
				}
				keyValue = lineRead.split(tcSeparateSign);

				if (keyValue != null && keyValue.length > 1
						&& keyValue[0].contains(MAIN_ST_PATTERN)) {
					pattern = Pattern.compile(keyValue[1]);
					mainStPatternArrayList.add(pattern);
					LOGGER.info("Add pattern to mainStPatternArrayList:"
							+ pattern.toString());

				} else if (keyValue != null && keyValue.length > 1
						&& keyValue[0].contains(FROM_PATTERN)) {
					pattern = Pattern.compile(keyValue[1]);
					fromPatternArrayList.add(pattern);
					LOGGER.info("Add pattern to fromPatternArrayList:"
							+ pattern.toString());

				} else if (keyValue != null && keyValue.length > 1
						&& keyValue[0].contains(TO_PATTERN)) {
					pattern = Pattern.compile(keyValue[1]);
					toPatternArrayList.add(pattern);
					LOGGER.info("Add pattern to toPatternArrayList:"
							+ pattern.toString());

				} else {
					LOGGER.info("Unknown pattern: " + keyValue[1]);
				}

			} // End of while

			LOGGER.info("Load patterns successfully");
			return true;
		} catch (FileNotFoundException ex) {
			LOGGER.fatal("Patterns file:" + PATTERN_FILE
					+ " does not exist, program will terminate now ("
					+ ex.getMessage() + ")");
			return false;
		} catch (Exception ex) {
			LOGGER.fatal("Parse pattern error, program will terminate now ("
					+ ex.getMessage() + ")");
			return false;
		} finally {
			if (buffReader != null) {
				try {
					buffReader.close();
				} catch (IOException e) {
					buffReader = null;
				}
			}
		}
	} // End of loadPatterns
	
	//#1
	private boolean loadFormat(){
		BufferedReader buffReader = null;
    	String lineRead = null;
    	String[] keyValue = null;
    	this.formatMap = new HashMap<String, List<Object>>();
		LOGGER.info("Start to load format resource.");
		try {
			buffReader = new BufferedReader(new FileReader(FORMAT_FILE));
			while ((lineRead = buffReader.readLine()) != null) {
				if (lineRead.length() < tcSeparateSign.length() + 2
						|| lineRead.startsWith("#")) {
					LOGGER.info("Empty or comment line, skipped:" + lineRead);
					continue;
				}
				keyValue = lineRead.split(tcSeparateSign);
				if (keyValue != null && keyValue.length > 1) {
					LOGGER.info("FORMAT: " + keyValue[0] + " = "
							+ keyValue[1]);
					if(keyValue[0] != null && keyValue[0].startsWith(LOCATION_FORMAT)){
						if(this.formatMap.get(LOCATION_FORMAT) == null){
							this.formatMap.put(LOCATION_FORMAT, new ArrayList<Object>());
						}
						this.formatMap.get(LOCATION_FORMAT)
						.add(new String[]{keyValue[0].replaceAll(LOCATION_FORMAT, ""),keyValue[1]});
					}						
				}
			} // End of while

			LOGGER.info("Load format successfully");
			return true;
		} catch (FileNotFoundException ex) {
			LOGGER.fatal("Format file:" + FORMAT_FILE
					+ " does not exist, program will terminate now ("
					+ ex.getMessage() + ")");
			return false;
		} catch (Exception ex) {
			LOGGER.fatal("Parse format error, program will terminate now ("
					+ ex.getMessage() + ")");
			return false;
		} finally {
			try {
				if (buffReader != null) {
					buffReader.close();
				}
			} catch (IOException e) {
				buffReader = null;
			}
		}
	}
	public String formatTiltel(String title){
		if(title == null || title.trim().equals("")){
			return null;
		}
		LOGGER.debug("Before format: " + title);
		
		return title;
	}
	public String formatLocation(String location){
    	if(location == null || location.trim().equals("")){
    		return null;
    	}
    	LOGGER.debug("Before format: " + location);
    	if(this.formatMap != null){
    		List<Object> formatList = this.formatMap.get(LOCATION_FORMAT);
    		if(formatList != null && formatList.size() > 0){
    			for(Object item: formatList){
    				String[] format = (String[]) item;
    				if(format.length == 2){
    				     location = location.replaceAll(format[0], format[1]).trim();	
    				}
    			}
    		}
    	}
    	LOGGER.debug("After format: " + location);
    	return location;
    }// end of #1

	/**
	 * For add extend event type,design by star .bug 6323
	 */
	private boolean loadEventTypeProperties() {
		BufferedReader buffReader = null;
		LOGGER.info("Start to load properties");
		String lineRead;
		eventTypeExtendMap = new LinkedHashMap<String, String>();
		try {
			buffReader = new BufferedReader(new FileReader(EVENT_TYPE_EXTEND));

			while ((lineRead = buffReader.readLine()) != null) {
				if (lineRead.length() < 0) {
					LOGGER.info("Empty or comment line, skipped:" + lineRead);
					continue;
				}
				if (lineRead.startsWith("KEYWORD")) {
					continue;
				}
				String[] keyValue = lineRead.split(",");
				if (keyValue.length == 2) {
					eventTypeExtendMap.put(keyValue[0].toUpperCase(), keyValue[1].toUpperCase());
				}

			}
			LOGGER.info("EventTypeExtend loaded successfully");
			buffReader.close();
			return true;

		} catch (FileNotFoundException ex) {
			LOGGER.fatal("Properties file:" + EVENT_TYPE_EXTEND + " does not exist, program will terminate now ("
					+ ex.getMessage() + ")");
			return false;
		} catch (Exception ex) {
			LOGGER.fatal("Parse properties error, program will terminate now (" + ex.getMessage() + ")");
			return false;
		} finally {
			buffReader = null;
		}

	}

}// end of class
