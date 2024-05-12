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
import java.nio.file.Path;
import java.nio.file.Paths;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.emf.ecore.util.ECrossReferenceAdapter;

import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.DirectedAcyclicGraph;
import org.slf4j.Logger;
import org.w3c.dom.Document;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import com.opencsv.CSVReaderHeaderAware;
import com.opencsv.exceptions.CsvValidationException;

import io.opencaesar.oml.dsl.OmlStandaloneSetup;
import io.opencaesar.oml.util.OmlConstants;

public class Taxonomy2Oml {
	
	protected final Logger logger;
	protected final List<String> inputPaths;
	protected final String outputPath;
	protected final String map_file;
	
	protected final Map<String, URI> iriByDeclName = new HashMap<>();
	protected final Map<URI, String> outputFn = new HashMap<>();
	
	protected final Map<String, Node> sbcById = new HashMap<>();
	protected final Map<String, String> idByDn = new HashMap<>();
	protected final Map<String, String> idByName = new HashMap<>();
	
	protected final DirectedAcyclicGraph<Node, DefaultEdge> sbcSuper = new DirectedAcyclicGraph<Node, DefaultEdge>(DefaultEdge.class);
	
	/**
	 * Constructs a new instance
	 * 
	 */
	public Taxonomy2Oml(Logger logger, List<String> inputPaths, String outputPath, String map_file) {
		this.logger = logger;
		this.inputPaths = inputPaths;
		this.outputPath = outputPath;
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
		XPathExpression topPackageXPath = xPath.compile(topPackageString);
		Map<String, Node> packages = new HashMap<>();

		logger.info("load documents");
		inputPaths.forEach(pathString -> {
			try {
				Path inputPath = Paths.get(pathString);
				Files.walk(inputPath)
				.filter(Files::isRegularFile)
                .filter(p -> pattern.matcher(p.getFileName().toString()).matches())
				.forEach(filePath -> {
					logger.info("document file path " + filePath.toString());
					String dirName = filePath.getParent().toString();
					Document doc = null;
					try {
						doc = builder.parse(new FileInputStream(filePath.toString()));
						doc.getDocumentElement().normalize();
					} catch (SAXException | IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
					try {
						NodeList topNodes = (NodeList) topPackageXPath.evaluate(doc, XPathConstants.NODESET);
						if (topNodes.getLength() == 0) {
							logger.error("no library package found for " + filePath);
							throw(new RuntimeException());
						}
						Node topPackage = topNodes.item(0);
						NamedNodeMap topPackageAttributes = topPackage.getAttributes();
						String declaredName = topPackageAttributes.getNamedItem("declaredName").getNodeValue();
						URI iri = makeIri(dirName, declaredName);
						logger.info("  document iri " + iri);
						iriByDeclName.put(declaredName, iri);
						
						String fn = makeOutputFn(outputPath, inputPath, filePath);
						logger.info("  output file path " + fn);
						outputFn.put(iri, fn);
						
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
		
		OmlStandaloneSetup.doSetup();
		
		ResourceSet outputResourceSet = new ResourceSetImpl();
		outputResourceSet.getLoadOptions().put(OmlConstants.RESOLVE_IRI_USING_RESOURCE_SET, true);
		outputResourceSet.eAdapters().add(new ECrossReferenceAdapter());
		
		/*
		 * Build graph of taxonomy edges.
		 */
		
		XPathExpression ownedRelationshipXPath = xPath.compile("ownedRelationship[@type='sysml:OwningMembership']/ownedRelatedElement");
		packages.forEach((packageName, node) -> {
			NodeList sbcs = null;
			try {
				sbcs = (NodeList) ownedRelationshipXPath.evaluate(node, XPathConstants.NODESET);
			} catch (XPathExpressionException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			for (int i = 0; i < sbcs.getLength(); i++) {
				Node sbc = sbcs.item(i);
				NamedNodeMap sbcAttributes = sbc.getAttributes();
				Node dnNode = sbcAttributes.getNamedItem("declaredName");
				if (dnNode != null) {
					String dn = dnNode.getNodeValue();
					String tp = sbcAttributes.getNamedItem("xsi:type").getNodeValue();
					String id = sbcAttributes.getNamedItem("elementId").getNodeValue();
					String name = packageName + "::" + dn;
					
					sbcById.put(id, sbc);
					idByDn.put(dn, id);
					idByName.put(name, id);
					
					sbcSuper.addVertex(sbc);
					
//					logger.info("class " + name + " type " + tp + " id " + id);
				}
			}
		});
		
		return "Hello World";
	}
	
	private static URI makeIri(String path, String stem) {
		String p = path.replaceAll("\\A.*/sysml.library.xmi", "http://omg.org/SysML-v2");
		return URI.createURI((p + "/" + stem).replaceAll("\\s+", "-"));
	}
	
	private static String makeOutputFn(String op, Path sp, Path fp) {
		Path trail = Paths.get(fp.toString().replace(sp.toString(), ""));
		String path = op + "/build/oml/omg.org/SysML-v2/" + trail.getParent().toString();
		String stem = trail.getFileName().toString().replaceAll("\\..*$", ".oml");
		return (path + "/" + stem).replaceAll("\\/+", "/");
	}
}
