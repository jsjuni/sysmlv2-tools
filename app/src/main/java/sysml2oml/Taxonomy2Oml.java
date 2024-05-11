package sysml2oml;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;
import java.nio.file.Files;
import java.nio.file.Paths;

import org.slf4j.Logger;

import com.opencsv.CSVReaderHeaderAware;
import com.opencsv.exceptions.CsvValidationException;

public class Taxonomy2Oml {
	
	protected final Logger logger;
	protected final List<String> inputPaths;
	protected final String map_file;
	
	/**
	 * Constructs a new instance
	 * 
	 */
	public Taxonomy2Oml(Logger logger, List<String> inputPaths, String map_file) {
		this.logger = logger;
		this.inputPaths = inputPaths;
		this.map_file = map_file;
	}
	
	public String run() throws CsvValidationException, FileNotFoundException, IOException {
		
		/*
		 * Load implicit supertypes map.
		 */
		
		@SuppressWarnings("resource")
		Map<String, String> values = new CSVReaderHeaderAware(new FileReader(map_file)).readMap();
		Map<String, String> st_map = new HashMap<>();
		values.forEach((v1, v2) -> {
			st_map.put(v1, v2);
		});
		
		/*
		 * Find all XMI files in path and parse.
		 */
		
		Pattern pattern = Pattern.compile(".*\\.(kermlx|sysmlx)");
		inputPaths.forEach(path_string -> {
			try {
				Files.walk(Paths.get(path_string))
				.filter(Files::isRegularFile)
                .filter(p -> pattern.matcher(p.getFileName().toString()).matches())
				.forEach(path -> {
					logger.info("found " + path.toString());
				});
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		});
		
		return "Hello World";
	}
}
