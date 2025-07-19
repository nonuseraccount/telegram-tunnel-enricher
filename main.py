# -*- coding: utf-8 -*-
"""
Proxy Data Loader, Processor & Enricher
=======================================

Author: Unavailable User (Conceptual Request)
Developed by: Gemini
Date: 2025-07-16
Version: 6.3.0

Project Overview:
-----------------
This script is a comprehensive, multi-stage data pipeline for fetching,
processing, enriching, and organizing proxy configurations. It is designed for
robustness, modularity, and high performance.

Required Libraries:
-------------------
To run this script, you must install the necessary Python libraries:
pip install requests tqdm dnspython geoip2-database jdatetime

Pipeline Stages:
----------------
1.  **Cleanup:** (Optional) Deletes the previous output directory for a fresh start.
2.  **Load:** The `DataLoader` class fetches raw data from URLs or local files.
3.  **Process:** The `ConfigProcessor` class performs initial separation of configs
    by client type and protocol.
4.  **Enrich:** The `EnrichmentProcessor` class validates and enriches 'plain'
    configs with DNS, connectivity, and geo-location data.
5.  **Organize & Save:** The `OutputOrganizer` class takes the final enriched
    configs and saves them into a detailed, multi-faceted directory structure
    in both raw and base64 formats, injecting dynamic headers and footers.

"""

import json
import logging
import os
import re
import sys
import base64
import socket
import ipaddress
import uuid
import shutil
from collections import defaultdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Union
from urllib.parse import urlparse, parse_qs, unquote, urlunsplit
from datetime import timezone, timedelta

# Third-party imports - ensure these are installed via pip
try:
    import dns.resolver
    import geoip2.database
    import requests
    from tqdm.auto import tqdm
    import jdatetime
except ImportError as e:
    print(f"Error: A required library is missing. {e}")
    print("Please install all required libraries by running:")
    print("pip install requests tqdm dnspython geoip2-database jdatetime")
    sys.exit(1)


# ================================================================
# 1. CONFIGURATION & CONSTANTS
# ================================================================

# --- Main Config ---
DATA_DIRECTORY = Path("data")
CONFIG_FILE_NAME = DATA_DIRECTORY / "subscription_urls.json"
DEFAULT_CHANNEL_CONFIG_SOURCE = "/archive_files/archive_channel_configs.json"
DEFAULT_SUBSCRIPTION_CONFIGS_SOURCE = "/archive_files/archive_subscription_configs.json"

# --- Enrichment Config ---
ENRICHMENT_SETTINGS_FILE = DATA_DIRECTORY / "enrichment_settings.json"
DEFAULT_ENRICHMENT_SETTINGS = {
    "ENABLE_CLEANUP_ON_START": True,
    "ENABLE_CONNECTIVITY_CHECK_CHANNELS": False,
    "ENABLE_CONNECTIVITY_CHECK_SUBSCRIPTIONS": False,
    "PROTOCOLS_TO_CONNECTIVITY_CHECK": ["vless", "vmess", "trojan", "ss", "socks4", "socks5", "http", "https"],
    "PROTOCOLS_REQUIRING_UUID_CHECK": ["vless", "vmess", "tuic"],
    "TITLE_FORMAT": "🔒 {protocol}-{network}-{security} {flag} {country_code}-{ip}:{port}",
    "GEOIP_DATABASE_URL": "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-Country.mmdb",
    "SIGNATURE_TITLE": "👨🏻‍💻 DEVELOPED-BY UNAVAILABLE-USER 📲 FOLLOW-CONTACT-GITHUB NONUSERACCOUNT",
    "ADVERTISEMENT_TITLES": [
        "🤖 JOIN-TELEGRAM-CHANNEL 💻 @NEUTRINOGATE"
    ]
}

# --- Static Constants ---
APP_LOGGER_NAME = "ProxyPipeline"
OUTPUT_DIRECTORY = Path("output")
GEOIP_DIR = Path("geoip-lite")
GEOIP_DATABASE_PATH = GEOIP_DIR / "GeoLite2-Country.mmdb"

PROTOCOL_MAP = {
    "shadowsocks": "SS", "ss": "SS", "socks4": "SOCKS", "socks5": "SOCKS",
    "vless": "VLESS", "vmess": "VMESS", "trojan": "TROJAN", "trojan-go": "TROJAN",
    "naive": "NAIVE", "hy2": "HYSTERIA", "hysteria": "HYSTERIA",
    "tuic": "TUIC", "anytls": "ANYTLS",
    "http": "HTTP", "https": "HTTP"
}

PROTOCOL_CONSOLIDATION_MAP = {
    "hy2": "hysteria",
    "trojan-go": "trojan",
    "ss": "shadowsocks",
    "socks4": "shadowsocks",
    "socks5": "shadowsocks"
}

# ================================================================
# 2. UTILITY & LOGGER SETUP
# ================================================================

class SuppressWarningsFilter(logging.Filter):
    """A logging filter to suppress messages below the ERROR level."""
    def filter(self, record):
        return record.levelno != logging.WARNING

class ColorFormatter(logging.Formatter):
    """A custom logging formatter that adds color to log levels for readability."""
    GREY, YELLOW, RED, RESET = "\x1b[38;20m", "\x1b[33;20m", "\x1b[31;20m", "\x1b[0m"
    FORMAT = "%(asctime)s [%(levelname)s] - %(message)s"
    FORMATS = {
        logging.DEBUG: GREY + FORMAT + RESET,
        logging.INFO: GREY + FORMAT + RESET,
        logging.WARNING: YELLOW + FORMAT + RESET,
        logging.ERROR: RED + FORMAT + RESET,
        logging.CRITICAL: RED + FORMAT + RESET,
    }
    def format(self, record):
        log_fmt = self.FORMATS.get(record.levelno)
        formatter = logging.Formatter(log_fmt, datefmt="%Y-%m-%d %H:%M:%S")
        return formatter.format(record)

def setup_logger() -> logging.Logger:
    """Sets up an isolated, color-coded logger for the application."""
    logger = logging.getLogger(APP_LOGGER_NAME)
    logger.setLevel(logging.INFO)
    logger.propagate = False
    if logger.hasHandlers(): logger.handlers.clear()
    console_handler = logging.StreamHandler(sys.stdout)
    console_handler.setFormatter(ColorFormatter())
    console_handler.addFilter(SuppressWarningsFilter()) # Add the filter here
    logger.addHandler(console_handler)
    return logger

def get_country_flag(country_code: str) -> str:
    """Converts a two-letter country code to its corresponding flag emoji."""
    if not country_code or country_code == "NA":
        return "🏴‍☠️"
    return "".join(chr(127397 + ord(char)) for char in country_code.upper())

def is_valid_ip_address(ip: str) -> bool:
    """Validates whether a string is a valid IPv4 or IPv6 address."""
    try:
        ipaddress.ip_address(ip)
        return True
    except ValueError:
        return False

def is_valid_base64(s: str) -> bool:
    """Checks if a string is valid Base64."""
    try:
        return base64.b64encode(base64.b64decode(s)) == s.encode()
    except Exception:
        return False

# ================================================================
# 3. STAGE 1: DIRECTORY CLEANER
# ================================================================

class DirectoryCleaner:
    """Handles the cleanup of the output directory."""
    def __init__(self, directory: Path, log: logging.Logger):
        self.directory = directory
        self.log = log

    def run(self):
        self.log.info("--- Starting Cleanup Stage ---")
        if self.directory.exists():
            try:
                shutil.rmtree(self.directory)
                self.log.info(f"Successfully removed old output directory: '{self.directory}'")
            except OSError as e:
                self.log.error(f"Error removing directory {self.directory}: {e}")
        else:
            self.log.info("Output directory does not exist, no cleanup needed.")
        
        self.directory.mkdir(exist_ok=True)

# ================================================================
# 4. STAGE 2: CORE DATA LOADING CLASS
# ================================================================

class DataLoader:
    """A class dedicated to loading data from specified sources."""
    def __init__(self, config: Dict[str, str], log: logging.Logger):
        self.channel_source = config["channel_config"]
        self.subscription_source = config["subscription_configs"]
        self.log = log

    def _load_single_source(self, source: str, description: str) -> Optional[Dict[str, Any]]:
        if source.lower().startswith(('http://', 'https://')):
            self.log.info(f"Fetching {description} from URL...")
            try:
                with requests.get(source, stream=True, timeout=30) as r:
                    r.raise_for_status()
                    total_size = int(r.headers.get('content-length', 0))
                    pbar = tqdm(total=total_size, unit='iB', unit_scale=True, desc=f"Downloading {os.path.basename(source)}")
                    content = b""
                    for data in r.iter_content(1024): pbar.update(len(data)); content += data
                    pbar.close()
                    return json.loads(content.decode('utf-8'))
            except (requests.exceptions.RequestException, json.JSONDecodeError) as e:
                self.log.error(f"Failed to load URL '{source}': {e}"); return None
        else:
            self.log.info(f"Loading {description} from local path: {source}")
            try:
                with open(source, 'r', encoding='utf-8') as f: return json.load(f)
            except (FileNotFoundError, json.JSONDecodeError) as e:
                self.log.error(f"Failed to load file '{source}': {e}"); return None

    def run(self) -> Tuple[Optional[Dict[str, Any]], Optional[Dict[str, Any]]]:
        self.log.info("--- Starting Data Loading Stage ---")
        channel_data = self._load_single_source(self.channel_source, "channel configs")
        subscription_data = self._load_single_source(self.subscription_source, "subscription configs")
        return channel_data, subscription_data

# ================================================================
# 5. STAGE 3: INITIAL CONFIG PROCESSING CLASS
# ================================================================

class ConfigProcessor:
    """Processes raw loaded data to separate configurations by client type and protocol."""
    def __init__(self, channel_data: Dict[str, Any], subscription_data: Dict[str, Any], log: logging.Logger):
        self.channel_data = channel_data; self.subscription_data = subscription_data; self.log = log

    def _get_config_details(self, config_url: str) -> Tuple[str, str]:
        if config_url.startswith("nekoray://"):
            client, protocol = "nekoray", (re.search(r"nekoray://(\w+)#", config_url) or [None, "unknown"])[1].lower()
        elif config_url.startswith("sn://"):
            client, protocol = "singbox", (re.search(r"sn://(\w+)\?", config_url) or [None, "unknown"])[1].lower()
        else:
            client, protocol = "plain", (re.search(r"^(\w+)(?:\+https|\+quic)?://", config_url) or [None, "unknown"])[1].lower()
        return client, protocol

    def _process_source_dict(self, source_data: Dict[str, Any], description: str) -> Dict[str, Dict[str, Dict[str, List[str]]]]:
        self.log.info(f"Performing initial processing on {len(source_data)} {description} sources...")
        structured_data = {}
        for source_identifier, content in tqdm(source_data.items(), desc=f"Initial Processing ({description}s)"):
            categorized_configs = defaultdict(lambda: defaultdict(list))
            all_configs_from_source = []
            if isinstance(content, dict):
                for config_list in content.values():
                    if isinstance(config_list, list): all_configs_from_source.extend(config_list)
            elif isinstance(content, list): all_configs_from_source.extend(content)
            
            for config_str in set(all_configs_from_source):
                if isinstance(config_str, str):
                    client, protocol = self._get_config_details(config_str)
                    categorized_configs[client][protocol].append(config_str)
            
            if categorized_configs:
                structured_data[source_identifier] = {k: dict(sorted(v.items())) for k, v in sorted(categorized_configs.items())}
        return structured_data

    def run(self) -> Tuple[Dict, Dict]:
        self.log.info("--- Starting Initial Data Processing Stage ---")
        processed_channels = self._process_source_dict(self.channel_data, "channel")
        processed_subscriptions = self._process_source_dict(self.subscription_data, "subscription")
        return processed_channels, processed_subscriptions

# ================================================================
# 6. STAGE 4: ADVANCED ENRICHMENT PROCESSING CLASS
# ================================================================

class EnrichmentProcessor:
    """Performs advanced, configurable processing on 'plain' configurations."""
    def __init__(self, processed_data: Dict, settings: Dict, log: logging.Logger, source_type: str):
        self.data = processed_data
        self.settings = settings
        self.log = log
        self.source_type = source_type # 'channels' or 'subscriptions'
        self.geoip_reader = self._load_geoip_database()
        self.dns_resolver = dns.resolver.Resolver()
        self.dns_resolver.nameservers = ['8.8.8.8', '1.1.1.1']
        self.failures = []

    def _load_geoip_database(self) -> Optional[geoip2.database.Reader]:
        GEOIP_DIR.mkdir(exist_ok=True)
        if not GEOIP_DATABASE_PATH.exists():
            self.log.info(f"GeoIP database not found. Attempting to download...")
            url = self.settings.get("GEOIP_DATABASE_URL")
            try:
                with requests.get(url, stream=True, timeout=60) as r:
                    r.raise_for_status()
                    total_size = int(r.headers.get('content-length', 0))
                    pbar = tqdm(total=total_size, unit='iB', unit_scale=True, desc="Downloading GeoLite2-Country.mmdb")
                    with GEOIP_DATABASE_PATH.open('wb') as f:
                        for chunk in r.iter_content(chunk_size=8192): pbar.update(len(chunk)); f.write(chunk)
                    pbar.close()
                self.log.info(f"Successfully downloaded GeoIP database to '{GEOIP_DATABASE_PATH}'.")
            except Exception as e:
                self.log.error(f"Failed to download GeoIP database: {e}"); return None
        
        try: return geoip2.database.Reader(GEOIP_DATABASE_PATH)
        except Exception as e:
            self.log.error(f"Failed to load GeoIP database from '{GEOIP_DATABASE_PATH}': {e}"); return None

    def _resolve_host(self, hostname: str, original_config_str: str) -> List[str]:
        if is_valid_ip_address(hostname):
            return [hostname]
        if any(len(label) > 63 for label in hostname.split('.')):
            self.failures.append({"config": original_config_str, "reason": f"Invalid Hostname (label > 63 chars): {hostname}"})
            return []
        ips = set()
        try:
            for rdata in self.dns_resolver.resolve(hostname, 'A', raise_on_no_answer=False): ips.add(rdata.to_text())
            for rdata in self.dns_resolver.resolve(hostname, 'AAAA', raise_on_no_answer=False): ips.add(rdata.to_text())
        except (dns.exception.DNSException, dns.name.LabelTooLong) as e:
            self.failures.append({"config": original_config_str, "reason": f"DNS Resolution Failed for {hostname}: {e}"})
            return []
        return list(ips)

    def _check_port_connectivity(self, ip: str, port: int, timeout: int = 1) -> bool:
        try:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
                sock.settimeout(timeout)
                return sock.connect_ex((ip, port)) == 0
        except socket.gaierror: # Handles "Address family for hostname not supported"
            return False

    def _get_country_code(self, ip: str) -> str:
        if not self.geoip_reader: return "NA"
        try: return self.geoip_reader.country(ip).country.iso_code or "NA"
        except geoip2.errors.AddressNotFoundError: return "NA"

    def _parse_config(self, config_str: str) -> Optional[Dict[str, Any]]:
        """Master parser to delegate to protocol-specific parsers."""
        try:
            # Sanitize HTML entities like &amp;
            config_str = unquote(config_str)

            if config_str.startswith("vmess://"):
                b64_part = config_str.replace("vmess://", "").split('#')[0]
                decoded_json = base64.b64decode(b64_part + "=" * (-len(b64_part) % 4)).decode('utf-8')
                data = json.loads(decoded_json)
                
                hostname = data.get("add", "")
                port = int(data.get("port", 0))
                if not hostname or not port: return None

                if "vmess" in self.settings.get("PROTOCOLS_REQUIRING_UUID_CHECK", []):
                    try: uuid.UUID(data.get("id"))
                    except (ValueError, TypeError): raise ValueError("Invalid VMess UUID")

                return {
                    "protocol": "vmess", "hostname": hostname, "port": port,
                    "network_type": data.get("net", "na").lower(),
                    "security_type": "TLS" if data.get("tls") in ["tls", True] else "NTLS",
                    "original_config": config_str, "data": data
                }
            else: # Handle all other URI-based schemes
                parsed_uri = urlparse(config_str)
                if not all([parsed_uri.scheme, parsed_uri.hostname, parsed_uri.port]): return None

                query_params = {k.lower(): v[0] for k, v in parse_qs(parsed_uri.query).items()}
                
                if query_params.get("security") == "reality": security_type = "RLTY"
                elif query_params.get("security") == "tls": security_type = "TLS"
                else: security_type = "NTLS"
                
                protocol = parsed_uri.scheme.lower().replace("+https", "").replace("+quic", "")
                
                # Specific validation for Shadowsocks
                if protocol == "ss":
                    userinfo = unquote(parsed_uri.username) if parsed_uri.username else ''
                    if not is_valid_base64(userinfo):
                        raise ValueError("Invalid Shadowsocks userinfo (not Base64)")

                if protocol in self.settings.get("PROTOCOLS_REQUIRING_UUID_CHECK", []):
                    try: uuid.UUID(parsed_uri.username)
                    except (ValueError, TypeError): raise ValueError("Invalid UUID")

                raw_network_type = query_params.get("type", "na").lower()
                if 'http' in raw_network_type: network_type = 'http'
                elif raw_network_type == 'kcp': network_type = 'tcp'
                elif raw_network_type in ['grpc', 'tcp', 'ws', 'udp', 'quic']: network_type = raw_network_type
                elif raw_network_type in ['raw', 'tel', 'none']: return None # Discard
                else: network_type = 'na'
                
                if protocol in ["hysteria", "hy2", "tuic"]: network_type = "udp"
                if protocol == "anytls": security_type = "TLS"

                return {
                    "protocol": protocol,
                    "hostname": parsed_uri.hostname, "port": parsed_uri.port,
                    "network_type": network_type,
                    "security_type": security_type,
                    "original_config": config_str, "data": parsed_uri
                }
        except Exception as e:
            self.failures.append({"config": config_str, "reason": f"Parsing Error: {e}"})
            return None

    def _enrich_and_rebuild(self, parsed_info: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Takes parsed info, enriches it, and rebuilds the final config strings."""
        enriched_configs = []
        resolved_ips = self._resolve_host(parsed_info["hostname"], parsed_info["original_config"])
        if not resolved_ips: return []

        check_key = f"ENABLE_CONNECTIVITY_CHECK_{self.source_type.upper()}"
        should_check_connectivity = self.settings.get(check_key, True)

        for ip in resolved_ips:
            if should_check_connectivity and parsed_info["protocol"] in self.settings.get("PROTOCOLS_TO_CONNECTIVITY_CHECK", []):
                if not self._check_port_connectivity(ip, parsed_info["port"]):
                    self.failures.append({"config": parsed_info["original_config"], "reason": f"Connectivity Check Failed for IP {ip}"})
                    continue

            country_code = self._get_country_code(ip)
            country_flag = get_country_flag(country_code)
            ip_version = "ipv6" if ":" in ip else "ipv4"
            ip_for_title = f"[{ip}]" if ip_version == "ipv6" else ip
            
            protocol_name = PROTOCOL_MAP.get(parsed_info["protocol"], parsed_info["protocol"].upper())
            
            title = self.settings.get("TITLE_FORMAT").format(
                protocol=protocol_name, network=parsed_info["network_type"].upper(), security=parsed_info["security_type"],
                flag=country_flag, country_code=country_code, ip=ip_for_title, port=parsed_info["port"]
            )

            if parsed_info["protocol"] == "vmess":
                vmess_data = parsed_info["data"].copy()
                vmess_data["add"] = ip
                vmess_data["ps"] = title
                new_b64 = base64.b64encode(json.dumps(vmess_data).encode('utf-8')).decode('utf-8')
                config_string = f"vmess://{new_b64}"
            else:
                uri_data = parsed_info["data"]
                netloc = f"{ip}:{uri_data.port}"
                if uri_data.username:
                    if uri_data.password: netloc = f"{uri_data.username}:{uri_data.password}@{netloc}"
                    else: netloc = f"{uri_data.username}@{netloc}"
                config_string = urlunsplit((uri_data.scheme, netloc, uri_data.path, uri_data.query, title))
            
            enriched_configs.append({
                "config_string": config_string,
                "protocol": parsed_info["protocol"],
                "network": parsed_info["network_type"],
                "security": parsed_info["security_type"],
                "ip_version": ip_version,
                "country_code": country_code
            })
                
        return enriched_configs

    def run(self) -> List[Dict[str, Any]]:
        self.log.info(f"--- Starting Advanced Enrichment Stage for '{self.source_type}' configs ---")
        if not self.geoip_reader: self.log.warning("GeoIP database not loaded. Country information will be unavailable.")

        all_enriched_configs = []
        for source, clients in tqdm(self.data.items(), desc=f"Enriching {self.source_type}"):
            if 'plain' in clients:
                all_plain_configs = [config for configs in clients['plain'].values() for config in configs]
                for config_str in tqdm(set(all_plain_configs), desc=f"Enriching {source}", leave=False):
                    parsed_info = self._parse_config(config_str)
                    if parsed_info:
                        all_enriched_configs.extend(self._enrich_and_rebuild(parsed_info))
        return all_enriched_configs

# ================================================================
# 6. STAGE 4: OUTPUT ORGANIZER CLASS
# ================================================================

class OutputOrganizer:
    """Categorizes and saves enriched configurations into a detailed directory structure."""
    def __init__(self, enriched_configs: List[Dict[str, Any]], base_path: Path, settings: Dict, log: logging.Logger):
        self.configs = enriched_configs
        self.base_path = base_path
        self.settings = settings
        self.log = log
        self.categorization_keys = {
            "protocol": "protocols",
            "network": "networks",
            "ip_version": "ip_versions",
            "security": "security",
            "country_code": "countries"
        }
        self.info_generator = self._InfoConfigGenerator(settings)

    class _InfoConfigGenerator:
        """A helper class to generate informational 'fake' configs."""
        def __init__(self, settings: Dict):
            self.settings = settings

        def _create_info_vless(self, title: str, port: int) -> str:
            """Creates a standardized VLESS config for informational purposes."""
            return f"vless://{uuid.uuid4()}@127.0.0.1:{port}?security=tls&type=tcp#{title}"

        def get_header_configs(self) -> List[str]:
            """Generates the datetime and advertisement configs."""
            header_configs = []
            # Datetime config
            iran_tz = timezone(timedelta(hours=3, minutes=30))
            now = jdatetime.datetime.now(tz=iran_tz)
            date_title = now.strftime("🔄 LATEST-UPDATE 📅 %a-%d-%B-%Y 🕔 %H:%M").upper()
            header_configs.append(self._create_info_vless(date_title, 1080))
            
            # Advertisement configs
            for i, ad_title in enumerate(self.settings.get("ADVERTISEMENT_TITLES", [])):
                header_configs.append(self._create_info_vless(ad_title, 2080 + i))
            
            return header_configs

        def get_footer_config(self) -> List[str]:
            """Generates the signature config."""
            title = self.settings.get("SIGNATURE_TITLE")
            return [self._create_info_vless(title, 8080)] if title else []

    def _save_files(self, path: Path, configs: List[str]):
        """Saves a list of configs to both raw and base64 encoded files."""
        path.parent.mkdir(parents=True, exist_ok=True)
        
        unique_configs = sorted(list(set(configs)))
        
        header = self.info_generator.get_header_configs()
        footer = self.info_generator.get_footer_config()
        
        final_configs = header + unique_configs + footer
        
        # Save raw file
        raw_content = "\n".join(final_configs)
        path.with_name(path.name + "_raw").write_text(raw_content, encoding='utf-8')
        
        # Save base64 file
        base64_content = base64.b64encode(raw_content.encode('utf-8')).decode('utf-8')
        path.with_name(path.name + "_base64").write_text(base64_content, encoding='utf-8')

    def save_aggregate_file(self, filename: str):
        """Saves a single file containing all configurations for this source."""
        self.log.info(f"Saving aggregate file '{filename}' for {self.base_path.name}...")
        all_config_strings = [c['config_string'] for c in self.configs]
        if all_config_strings:
            self._save_files(self.base_path / filename, all_config_strings)

    def _organize_by_primary_key(self, primary_key: str):
        """Organizes and saves configs based on a primary categorization key."""
        primary_dir_name = self.categorization_keys.get(primary_key)
        self.log.info(f"Organizing by primary key: '{primary_key}'...")
        
        secondary_keys = [k for k in self.categorization_keys if k != primary_key]
        
        primary_groups = defaultdict(list)
        for config in self.configs:
            protocol_key = config["protocol"]
            consolidated_protocol = PROTOCOL_CONSOLIDATION_MAP.get(protocol_key, protocol_key)
            
            if primary_key == "protocol":
                primary_groups[consolidated_protocol].append(config)
            else:
                primary_groups[config[primary_key]].append(config)
            
        for primary_value, group_configs in tqdm(primary_groups.items(), desc=f"Categorizing by {primary_key}"):
            primary_path = self.base_path / primary_dir_name / primary_value.lower()
            
            self._save_files(primary_path / "all", [c['config_string'] for c in group_configs])

            for secondary_key in secondary_keys:
                secondary_dir_name = self.categorization_keys.get(secondary_key)
                secondary_groups = defaultdict(list)
                for config in group_configs:
                    if secondary_key == "protocol":
                        protocol_key = config["protocol"]
                        consolidated_protocol = PROTOCOL_CONSOLIDATION_MAP.get(protocol_key, protocol_key)
                        secondary_groups[consolidated_protocol].append(config['config_string'])
                    else:
                        secondary_groups[config[secondary_key]].append(config['config_string'])
                
                for secondary_value, configs in secondary_groups.items():
                    secondary_path = primary_path / secondary_dir_name / secondary_value.lower()
                    self._save_files(secondary_path, configs)

    def run(self):
        """Runs the full organization process for all primary keys."""
        self.log.info(f"--- Starting Output Organization for {self.base_path.name} ---")
        if not self.configs:
            self.log.info("No enriched configs to organize for this source.")
            return

        self.save_aggregate_file("all_configs")
        for key in self.categorization_keys:
            self._organize_by_primary_key(key)

# ================================================================
# 7. MAIN EXECUTION BLOCK
# ================================================================

def main():
    """Main function to orchestrate the data loading and processing pipeline."""
    log = setup_logger()
    log.info("Starting Data Pipeline...")

    # --- Configuration File Management ---
    DATA_DIRECTORY.mkdir(exist_ok=True)
    config_path = CONFIG_FILE_NAME
    enrich_settings_path = ENRICHMENT_SETTINGS_FILE

    if not config_path.exists():
        log.info(f"Config file '{config_path}' not found. Creating from template.")
        with config_path.open('w', encoding='utf-8') as f:
            json.dump({ "channel_config": DEFAULT_CHANNEL_CONFIG_SOURCE, "subscription_configs": DEFAULT_SUBSCRIPTION_CONFIGS_SOURCE }, f, indent=4)
        log.info(f"A new '{config_path}' was created. Please edit it and run again.")
        sys.exit(0)

    if not enrich_settings_path.exists():
        log.info(f"Enrichment settings file '{enrich_settings_path}' not found. Creating with defaults.")
        with enrich_settings_path.open('w', encoding='utf-8') as f:
            json.dump(DEFAULT_ENRICHMENT_SETTINGS, f, indent=4)
        log.info(f"Default enrichment settings saved. You can customize this file.")

    try:
        with config_path.open('r', encoding='utf-8') as f: config = json.load(f)
        with enrich_settings_path.open('r', encoding='utf-8') as f: enrichment_settings = json.load(f)
    except json.JSONDecodeError as e:
        log.error(f"Could not parse a config file. Ensure it is valid JSON. Error: {e}"); sys.exit(1)
    
    # --- Stage 1: Cleanup ---
    if enrichment_settings.get("ENABLE_CLEANUP_ON_START", False):
        DirectoryCleaner(OUTPUT_DIRECTORY, log).run()

    # --- Pipeline Execution ---
    data_loader = DataLoader(config=config, log=log)
    channel_data, subscription_data = data_loader.run()
    if channel_data is None or subscription_data is None: log.error("Failed to load data sources. Aborting."); sys.exit(1)
    log.info("--- Data Loading Complete ---")

    processor = ConfigProcessor(channel_data=channel_data, subscription_data=subscription_data, log=log)
    processed_channel_data, processed_subscription_data = processor.run()
    log.info("--- Initial Processing Complete ---")
    
    enricher_channels = EnrichmentProcessor(processed_channel_data, enrichment_settings, log, 'channels')
    enriched_channels = enricher_channels.run()
    
    enricher_subscriptions = EnrichmentProcessor(processed_subscription_data, enrichment_settings, log, 'subscriptions')
    enriched_subscriptions = enricher_subscriptions.run()
    log.info("--- Enrichment Processing Complete ---")

    # --- Stage 4: Organize and Save Output ---
    OUTPUT_DIRECTORY.mkdir(exist_ok=True)
    
    # Organize Channel Data
    organizer_channels = OutputOrganizer(enriched_channels, OUTPUT_DIRECTORY / "channel_sources", enrichment_settings, log)
    organizer_channels.run()
    
    # Organize Subscription Data
    organizer_subscriptions = OutputOrganizer(enriched_subscriptions, OUTPUT_DIRECTORY / "subscription_sources", enrichment_settings, log)
    organizer_subscriptions.run()

    # Organize Collected (Combined) Data
    collected_configs = enriched_channels + enriched_subscriptions
    organizer_collected = OutputOrganizer(collected_configs, OUTPUT_DIRECTORY / "collected_sources", enrichment_settings, log)
    organizer_collected.run()

    # Save Failures
    all_failures = enricher_channels.failures + enricher_subscriptions.failures
    if all_failures:
        failures_output_path = OUTPUT_DIRECTORY / "enrichment_failures.json"
        with failures_output_path.open('w', encoding='utf-8') as f:
            json.dump(all_failures, f, indent=4, ensure_ascii=False)
        log.error(f"Saved {len(all_failures)} failed configs to '{failures_output_path}'")

    log.info("--- Pipeline Finished Successfully ---")


if __name__ == "__main__":
    main()
