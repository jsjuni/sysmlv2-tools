package sysml2oml;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.xpath.XPath;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathExpression;
import javax.xml.xpath.XPathExpressionException;
import javax.xml.xpath.XPathFactory;

import java.nio.file.Files;
import java.nio.file.Paths;

import org.slf4j.Logger;
import org.w3c.dom.Document;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

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
	
	public String run() throws CsvValidationException, FileNotFoundException, IOException, ParserConfigurationException, XPathExpressionException {
		
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
		DocumentBuilder builder = DocumentBuilderFactory.newInstance().newDocumentBuilder();
		XPath xPath = XPathFactory.newInstance().newXPath();
		String topPackageString = "Namespace/ownedRelationship[@type='sysml:OwningMembership']/ownedRelatedElement[@type='sysml:LibraryPackage']";
		String nestedPackageString = "ownedRelationship[@type='sysml:OwningMembership']/ownedRelatedElement[@type='sysml:Package']";
		XPathExpression topPackageXPath = xPath.compile(topPackageString);
		XPathExpression nestedPackageXPath = xPath.compile(nestedPackageString);
		Map<String, Node> packages = new HashMap<>();

		inputPaths.forEach(path_string -> {
			try {
				Files.walk(Paths.get(path_string))
				.filter(Files::isRegularFile)
                .filter(p -> pattern.matcher(p.getFileName().toString()).matches())
				.forEach(p -> {
					String fileName = p.toString();
					logger.info("found " + fileName);
					Document doc = null;
					try {
						doc = builder.parse(new FileInputStream(fileName));
						doc.getDocumentElement().normalize();
					} catch (SAXException | IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
					try {
						NodeList topNodes = (NodeList) topPackageXPath.evaluate(doc, XPathConstants.NODESET);
						if (topNodes.getLength() == 0) {
							logger.error("no top package found for " + fileName);
							throw(new RuntimeException());
						}
						Node topPackage = topNodes.item(0);
						NamedNodeMap topPackageAttributes = topPackage.getAttributes();
						String topPackageName = topPackageAttributes.getNamedItem("declaredName").getNodeValue();
						logger.info("library package " + topPackageName);
						packages.put(topPackageName, topPackage);
						
						 NodeList nestedNodes = (NodeList) nestedPackageXPath.evaluate(topPackage, XPathConstants.NODESET);
						 for (int i = 0; i < nestedNodes.getLength(); i++) {
							 Node node = nestedNodes.item(i);
							 NamedNodeMap packageAttributes = node.getAttributes();
							 String packageName = packageAttributes.getNamedItem("declaredName").getNodeValue();
							 logger.info("  nested package " + packageName);
							 packages.put(packageName, node);
						 }
						 
					} catch (XPathExpressionException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				});
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		});
		
		return "Hello World";
	}
}
