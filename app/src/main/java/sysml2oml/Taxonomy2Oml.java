package sysml2oml;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
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
import org.w3c.dom.Element;

import com.opencsv.CSVReaderHeaderAware;
import com.opencsv.exceptions.CsvValidationException;

import io.opencaesar.oml.Import;
import io.opencaesar.oml.ImportKind;
import io.opencaesar.oml.OmlFactory;
import io.opencaesar.oml.Vocabulary;
import io.opencaesar.oml.dsl.OmlStandaloneSetup;
import io.opencaesar.oml.util.OmlBuilder;
import io.opencaesar.oml.util.OmlConstants;

public class Taxonomy2Oml {
	
	protected final static String catalogStem = "catalog.xml";
	protected final Logger logger;
	protected final List<String> inputPaths;
	protected final List<String> bundles;
	protected final String outputPath;
	protected final String map_file;
	
	protected final Map<String, URI> iriByDeclName = new HashMap<>();
	protected final Map<URI, String> outputFn = new HashMap<>();
	protected final Map<URI, Node> packages = new HashMap<>();
	protected final Map<URI, Vocabulary> vocabularies = new HashMap<>();
	protected final Map<String, String> catalogMap = new HashMap<>();
	
	protected final Map<String, Map<String, String>> sbcById = new HashMap<>();
	protected final Map<String, String> idByDn = new HashMap<>();
	protected final Map<String, String> idByName = new HashMap<>();
	
	protected final DirectedAcyclicGraph<String, DefaultEdge> sbcSuper = new DirectedAcyclicGraph<String, DefaultEdge>(DefaultEdge.class);
	
	/**
	 * Constructs a new instance
	 * 
	 */
	public Taxonomy2Oml(Logger logger, List<String> inputPaths, List<String> bundles, String outputPath, String map_file) {
		this.logger = logger;
		this.inputPaths = inputPaths;
		this.bundles = bundles;
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

					/*
					 * Parse XMI document.
					 */
					
					Document doc = null;
					try {
						doc = builder.parse(new FileInputStream(filePath.toString()));
						doc.getDocumentElement().normalize();
					} catch (SAXException | IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
					try {
						
						/*
						 * Find Library Package.
						 */
						
						NodeList topNodes = (NodeList) topPackageXPath.evaluate(doc, XPathConstants.NODESET);
						if (topNodes.getLength() == 0) {
							logger.error("no library package found for " + filePath);
							throw(new RuntimeException());
						}
						Node topPackage = topNodes.item(0);
						NamedNodeMap topPackageAttributes = topPackage.getAttributes();
						
						/*
						 * Construct vocabulary IRI and cache it.
						 */
						
						String declaredName = topPackageAttributes.getNamedItem("declaredName").getNodeValue();
						URI iri = makeIri(dirName, declaredName);
						iriByDeclName.put(declaredName, iri);
						logger.info("  document iri " + iri);
						
						/*
						 * Construct output filename and cache it.
						 */
						
						String fn = makeOutputFn(outputPath, inputPath, filePath);
						logger.info("  output file path " + fn);
						outputFn.put(iri, fn);
						
						/*
						 * Cache document by IRI.
						 */
						
						packages.put(iri, topPackage);
						
						/*
						 * Create catalog entry for this document.
						 */
						
						catalogMap.put(makeCatalogStartString(inputPath, filePath), makeCatalogRewritePrefix(inputPath, filePath));
						
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
		logger.info(String.format("loaded %d documents", packages.size()));
		
		/*
		 * Add default catalog rule and write catalog.
		 */
		
		catalogMap.put("http://",  "src/oml");
		createOutputCatalog(outputPath, catalogMap);
		
		OmlStandaloneSetup.doSetup();
		
		ResourceSet outputResourceSet = new ResourceSetImpl();
		outputResourceSet.getLoadOptions().put(OmlConstants.RESOLVE_IRI_USING_RESOURCE_SET, true);
		outputResourceSet.eAdapters().add(new ECrossReferenceAdapter());
		
		logger.info("create oml factory");
		OmlFactory oml = OmlFactory.eINSTANCE;
		
		logger.info("create builder");
		OmlBuilder omlBuilder = new OmlBuilder(outputResourceSet);
		
		logger.info("start builder");
		omlBuilder.start();
		
		/*
		 * Create vocabularies.
		 */
		
		logger.info("create vocabularies");		
		Set<URI> outputResourceUris = new HashSet<>();
		packages.forEach((iri, pkg) -> {
			URI uri = URI.createFileURI(outputFn.get(iri));
			outputResourceUris.add(uri);
			NamedNodeMap at = pkg.getAttributes();
			Node packageNameNode = pkg.getAttributes().getNamedItem("declaredName");
			String packageName = packageNameNode.getNodeValue();
			
			/*
			 * Find elements that will become concepts.
			 */
			
			XPathExpression ownedRelationshipXPath = null;
			try {
				ownedRelationshipXPath = xPath.compile("ownedRelationship[@type='sysml:OwningMembership']/ownedRelatedElement");
			} catch (XPathExpressionException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			NodeList sbcs = null;
			try {
				sbcs = (NodeList) ownedRelationshipXPath.evaluate(pkg, XPathConstants.NODESET);
			} catch (XPathExpressionException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			for (int i = 0; i < sbcs.getLength(); i++) {
				Node sbc = sbcs.item(i);
				NamedNodeMap sbcAttributes = sbc.getAttributes();
				Node dnNode = sbcAttributes.getNamedItem("declaredName");
				if (dnNode == null) continue;
				String dn = dnNode.getNodeValue();
				Node tpNode = sbcAttributes.getNamedItem("xsi:type");
				if (dnNode.getNodeValue() == "sysml:Package");
				Node idNode = sbcAttributes.getNamedItem("elementId");
				String id = idNode.getNodeValue();
				Map<String, String> m = new HashMap<>();
				m.put("name", id);
				m.put("iri", iri.toString());
				sbcById.put(idNode.getNodeValue(), m);
				idByDn.put(dn, id);
				idByName.put(packageName, id);
				sbcSuper.addVertex(id);
			}

			vocabularies.put(iri,
					omlBuilder.createVocabulary(uri, iri.toString(), Paths.get(iri.toString()).getFileName().toString()));
			
			Import rdfsImport = oml.createImport();
			rdfsImport.setKind(ImportKind.EXTENSION);
			rdfsImport.setNamespace("http://www.w3.org/2000/01/rdf-schema#");
			rdfsImport.setPrefix("rdfs");
			rdfsImport.setOwningOntology(vocabularies.get(iri));
			
			/*
			 * Add concept definitions.
			 */
		
			
		});
		
		logger.info("finish builder");
		omlBuilder.finish();
		
		logger.info("save resources");
		outputResourceUris.forEach(outputResourceUri -> {
			logger.info("save " + outputResourceUri.toString());
			Resource outputResource = outputResourceSet.getResource(outputResourceUri, false);
			try {
				outputResource.save(Collections.EMPTY_MAP);
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		});
				
		return "Hello World";
	}
	
	private static Path trail(Path fp, Path sp) {
		return Paths.get(fp.toString().replace(sp.toString(), ""));
	}
	
	private static URI makeIri(String path, String stem) {
		String p = path.replaceAll("\\A.*/sysml.library.xmi", "http://omg.org/SysML-v2");
		return URI.createURI((p + "/" + stem).replaceAll("\\s+", "-"));
	}
	
	private static String makeOutputFn(String op, Path sp, Path fp) {
		Path trail = trail(fp, sp);
		String path = op + "/omg.org/SysML-v2/" + trail.getParent().toString();
		String stem = trail.getFileName().toString().replaceAll("\\..*$", ".oml");
		return (path + "/" + stem).replaceAll("\\/+", "/");
	}
	
	private static String makeCatalogStartString(Path sp, Path fp) {
		Path trail = trail(fp, sp);
		return "http://omg.org/SysML-v2" + trail.getParent().toString().replaceAll("\\s+", "-").replaceAll("\\/+", "/");
	}

	private static String makeCatalogRewritePrefix(Path sp, Path fp) {
		Path trail = trail(fp, sp);
		return "/omg.org/SysML-v2" + trail.getParent().toString().replaceAll("\\s+", "-").replaceAll("\\/+", "/");
	}
	
	private static void createOutputCatalog(String path, Map<String, String> map) {
		(new File(path)).mkdirs();
		
		String fn = path + "/" + catalogStem;
		FileWriter writer = null;
		try {
			writer = new FileWriter(fn);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		DocumentBuilder builder = null;
		try {
			builder = factory.newDocumentBuilder();
		} catch (ParserConfigurationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		Document doc = builder.newDocument();
		DOMSource source = new DOMSource(doc);
		Element cat = (Element) doc.createElement("catalog");
		cat.setAttribute("xmlns", "urn:oasis:names:tc:entity:xmlns:xml:catalog");
		cat.setAttribute("prefer", "public");
		doc.appendChild(cat);
		
		map.forEach((ss, rp) -> {
			Element srw = doc.createElement("rewriteURI");
			srw.setAttribute("uriStartString", ss);
			srw.setAttribute("rewritePrefix", rp);
			cat.appendChild(srw);
		});
		
		TransformerFactory transformerFactory = TransformerFactory.newInstance();
		Transformer transformer = null;
		try {
			transformer = transformerFactory.newTransformer();
		} catch (TransformerConfigurationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		transformer.setOutputProperty(OutputKeys.INDENT, "yes");
		transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "2");
		StreamResult result = new StreamResult(writer);
		try {
			transformer.transform(source, result);
		} catch (TransformerException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		try {
			writer.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}
