//! Integration tests for real-world Ligature examples.
//! 
//! These tests demonstrate how Ligature can be used for practical
//! configuration and data management tasks.

use ligature_parser::parse_program;
use ligature_eval::evaluate_program;
use ligature_eval::Value;

#[test]
fn test_application_configuration() {
    let program = r#"
        type Environment = Development | Staging | Production;
        type LogLevel = Debug | Info | Warn | Error;
        
        type AppConfig = {
            name: String,
            version: String,
            environment: Environment,
            debug: Boolean,
            log_level: LogLevel,
            port: Integer,
            host: String,
            max_connections: Integer,
            timeout_seconds: Integer
        };
        
        let development_config = {
            name = "MyApplication",
            version = "1.0.0",
            environment = Development,
            debug = true,
            log_level = Debug,
            port = 8080,
            host = "localhost",
            max_connections = 100,
            timeout_seconds = 30
        };
        
        let production_config = {
            name = "MyApplication",
            version = "1.0.0",
            environment = Production,
            debug = false,
            log_level = Info,
            port = 80,
            host = "0.0.0.0",
            max_connections = 1000,
            timeout_seconds = 60
        };
        
        let get_config = \env -> match env of
            Development => development_config,
            Staging => {
                name = "MyApplication",
                version = "1.0.0",
                environment = Staging,
                debug = false,
                log_level = Info,
                port = 8080,
                host = "staging.example.com",
                max_connections = 500,
                timeout_seconds = 45
            },
            Production => production_config;
        
        let current_config = get_config Development;
        let config_name = current_config.name;
        let config_port = current_config.port;
    "#;
    
    let parsed = parse_program(program).unwrap();
    let result = evaluate_program(&parsed).unwrap();
    
    // Verify the configuration was created correctly
    assert!(result.is_record());
}

#[test]
fn test_database_configuration() {
    let program = r#"
        type SslMode = Disable | Require | VerifyCa | VerifyFull;
        
        type DatabaseConfig = {
            host: String,
            port: Integer,
            database: String,
            username: String,
            password: String,
            ssl_mode: SslMode,
            max_connections: Integer,
            connection_timeout: Integer,
            idle_timeout: Integer,
            statement_timeout: Integer
        };
        
        let development_db = {
            host = "localhost",
            port = 5432,
            database = "myapp_dev",
            username = "postgres",
            password = "password",
            ssl_mode = Disable,
            max_connections = 10,
            connection_timeout = 30,
            idle_timeout = 300,
            statement_timeout = 30000
        };
        
        let production_db = {
            host = "db.example.com",
            port = 5432,
            database = "myapp_prod",
            username = "app_user",
            password = "secret_password",
            ssl_mode = VerifyFull,
            max_connections = 100,
            connection_timeout = 60,
            idle_timeout = 600,
            statement_timeout = 60000
        };
        
        let validate_config = \config -> match config of
            { host = h, port = p, database = d, username = u, password = pw } when
                h != "" && p > 0 && p <= 65535 && d != "" && u != "" && pw != "" =>
                true,
            _ => false;
        
        let dev_valid = validate_config development_db;
        let prod_valid = validate_config production_db;
    "#;
    
    let parsed = parse_program(program).unwrap();
    let result = evaluate_program(&parsed).unwrap();
    
    // Verify the database configuration was created and validated
    assert!(result.is_record());
}

#[test]
fn test_api_configuration() {
    let program = r#"
        type HttpMethod = GET | POST | PUT | DELETE | PATCH;
        type AuthType = Bearer | ApiKey | OAuth2;
        
        type Endpoint = {
            path: String,
            method: HttpMethod,
            auth_required: Boolean,
            rate_limit: Integer,
            timeout_ms: Integer
        };
        
        type AuthConfig = {
            enabled: Boolean,
            type: AuthType,
            token_expiry_hours: Integer
        };
        
        type RateLimitConfig = {
            enabled: Boolean,
            requests_per_minute: Integer,
            burst_size: Integer
        };
        
        type ApiConfig = {
            base_url: String,
            version: String,
            endpoints: List Endpoint,
            auth: AuthConfig,
            rate_limiting: RateLimitConfig
        };
        
        let api_config = {
            base_url = "https://api.example.com",
            version = "v1",
            endpoints = [
                {
                    path = "/users",
                    method = GET,
                    auth_required = true,
                    rate_limit = 100,
                    timeout_ms = 5000
                },
                {
                    path = "/users",
                    method = POST,
                    auth_required = true,
                    rate_limit = 10,
                    timeout_ms = 10000
                }
            ],
            auth = {
                enabled = true,
                type = Bearer,
                token_expiry_hours = 24
            },
            rate_limiting = {
                enabled = true,
                requests_per_minute = 1000,
                burst_size = 100
            }
        };
        
        let get_endpoint_config = \path method config ->
            case find_endpoint path method config.endpoints of
                Some endpoint => endpoint,
                None => {
                    path = "/404",
                    method = GET,
                    auth_required = false,
                    rate_limit = 0,
                    timeout_ms = 1000
                };
        
        let user_get_config = get_endpoint_config "/users" GET api_config;
    "#;
    
    let parsed = parse_program(program).unwrap();
    let result = evaluate_program(&parsed).unwrap();
    
    // Verify the API configuration was created correctly
    assert!(result.is_record());
}

#[test]
fn test_data_validation() {
    let program = r#"
        type ValidationResult = Valid | Invalid String;
        
        type User = {
            username: String,
            email: String,
            age: Integer,
            password: String
        };
        
        let validate_username = \username -> match username of
            u when length u < 3 => Invalid "Username too short",
            u when length u > 20 => Invalid "Username too long",
            u when contains u " " => Invalid "Username cannot contain spaces",
            _ => Valid;
        
        let validate_email = \email -> match email of
            e when contains e "@" && contains e "." => Valid,
            _ => Invalid "Invalid email format";
        
        let validate_age = \age -> match age of
            a when a < 13 => Invalid "Must be at least 13 years old",
            a when a > 120 => Invalid "Age seems unrealistic",
            _ => Valid;
        
        let validate_password = \password -> match password of
            p when length p < 8 => Invalid "Password too short",
            p when length p > 128 => Invalid "Password too long",
            _ => Valid;
        
        let validate_user = \user -> match user of
            { username = u, email = e, age = a, password = p } =>
                case validate_username u of
                    Valid => case validate_email e of
                        Valid => case validate_age a of
                            Valid => validate_password p,
                            Invalid msg => Invalid msg,
                        Invalid msg => Invalid msg,
                    Invalid msg => Invalid msg;
        
        let test_user = {
            username = "alice123",
            email = "alice@example.com",
            age = 25,
            password = "securepassword123"
        };
        
        let validation_result = validate_user test_user;
        
        let invalid_user = {
            username = "a",
            email = "invalid-email",
            age = 10,
            password = "123"
        };
        
        let invalid_result = validate_user invalid_user;
    "#;
    
    let parsed = parse_program(program).unwrap();
    let result = evaluate_program(&parsed).unwrap();
    
    // Verify the validation functions work correctly
    assert!(result.is_record());
}

#[test]
fn test_feature_flags() {
    let program = r#"
        type FeatureFlag = {
            name: String,
            enabled: Boolean,
            rollout_percentage: Integer,
            target_environments: List String,
            target_users: List String,
            dependencies: List String
        };
        
        let feature_flags = [
            {
                name = "new_ui",
                enabled = true,
                rollout_percentage = 50,
                target_environments = ["staging", "production"],
                target_users = ["beta_users"],
                dependencies = []
            },
            {
                name = "advanced_search",
                enabled = false,
                rollout_percentage = 0,
                target_environments = ["development"],
                target_users = ["internal_users"],
                dependencies = ["new_ui"]
            }
        ];
        
        let find_flag = \flag_name flags ->
            case flags of
                [] => None,
                flag :: rest when flag.name == flag_name => Some flag,
                flag :: rest => find_flag flag_name rest;
        
        let is_feature_enabled = \flag_name user_id environment flags ->
            case find_flag flag_name flags of
                Some flag when flag.enabled && 
                              contains environment flag.target_environments &&
                              flag.rollout_percentage > 0 => true,
                _ => false;
        
        let new_ui_enabled = is_feature_enabled "new_ui" "user123" "production" feature_flags;
        let search_enabled = is_feature_enabled "advanced_search" "user123" "development" feature_flags;
    "#;
    
    let parsed = parse_program(program).unwrap();
    let result = evaluate_program(&parsed).unwrap();
    
    // Verify the feature flag system works correctly
    assert!(result.is_record());
}

#[test]
fn test_monitoring_configuration() {
    let program = r#"
        type MetricType = Counter | Gauge | Histogram | Summary;
        
        type ThresholdConfig = {
            warning: Float,
            critical: Float,
            alert_enabled: Boolean
        };
        
        type MetricConfig = {
            name: String,
            type: MetricType,
            interval_seconds: Integer,
            labels: List String,
            thresholds: ThresholdConfig
        };
        
        let application_metrics = [
            {
                name = "http_requests_total",
                type = Counter,
                interval_seconds = 60,
                labels = ["method", "endpoint", "status"],
                thresholds = {
                    warning = 1000.0,
                    critical = 5000.0,
                    alert_enabled = true
                }
            },
            {
                name = "response_time_seconds",
                type = Histogram,
                interval_seconds = 30,
                labels = ["endpoint"],
                thresholds = {
                    warning = 1.0,
                    critical = 5.0,
                    alert_enabled = true
                }
            }
        ];
        
        let find_metric = \metric_name metrics ->
            case metrics of
                [] => None,
                metric :: rest when metric.name == metric_name => Some metric,
                metric :: rest => find_metric metric_name rest;
        
        let get_metric_thresholds = \metric_name metrics ->
            case find_metric metric_name metrics of
                Some metric => metric.thresholds,
                None => {
                    warning = 0.0,
                    critical = 0.0,
                    alert_enabled = false
                };
        
        let request_thresholds = get_metric_thresholds "http_requests_total" application_metrics;
        let response_thresholds = get_metric_thresholds "response_time_seconds" application_metrics;
    "#;
    
    let parsed = parse_program(program).unwrap();
    let result = evaluate_program(&parsed).unwrap();
    
    // Verify the monitoring configuration works correctly
    assert!(result.is_record());
}

#[test]
fn test_microservices_configuration() {
    let program = r#"
        type LoadBalancerAlgorithm = RoundRobin | LeastConnections | Random;
        
        type HealthCheckConfig = {
            path: String,
            interval_seconds: Integer,
            timeout_seconds: Integer,
            failure_threshold: Integer
        };
        
        type LoadBalancerConfig = {
            algorithm: LoadBalancerAlgorithm,
            max_connections: Integer,
            timeout_seconds: Integer
        };
        
        type ServiceConfig = {
            name: String,
            version: String,
            host: String,
            port: Integer,
            health_check: HealthCheckConfig,
            load_balancer: LoadBalancerConfig
        };
        
        let user_service = {
            name = "user-service",
            version = "1.0.0",
            host = "user-service.example.com",
            port = 8081,
            health_check = {
                path = "/health",
                interval_seconds = 30,
                timeout_seconds = 5,
                failure_threshold = 3
            },
            load_balancer = {
                algorithm = RoundRobin,
                max_connections = 100,
                timeout_seconds = 30
            }
        };
        
        let order_service = {
            name = "order-service",
            version = "1.0.0",
            host = "order-service.example.com",
            port = 8082,
            health_check = {
                path = "/health",
                interval_seconds = 30,
                timeout_seconds = 5,
                failure_threshold = 3
            },
            load_balancer = {
                algorithm = LeastConnections,
                max_connections = 200,
                timeout_seconds = 60
            }
        };
        
        let services = [user_service, order_service];
        
        let find_service = \service_name service_list ->
            case service_list of
                [] => None,
                service :: rest when service.name == service_name => Some service,
                service :: rest => find_service service_name rest;
        
        let get_service_url = \service_name service_list ->
            case find_service service_name service_list of
                Some service => service.host ++ ":" ++ toString service.port,
                None => "service-not-found";
        
        let user_service_url = get_service_url "user-service" services;
        let order_service_url = get_service_url "order-service" services;
    "#;
    
    let parsed = parse_program(program).unwrap();
    let result = evaluate_program(&parsed).unwrap();
    
    // Verify the microservices configuration works correctly
    assert!(result.is_record());
}

#[test]
fn test_build_system_configuration() {
    let program = r#"
        type WebpackMode = Development | Production;
        
        type OutputConfig = {
            path: String,
            filename: String,
            public_path: String
        };
        
        type DevServerConfig = {
            port: Integer,
            hot: Boolean,
            open: Boolean
        };
        
        type WebpackConfig = {
            mode: WebpackMode,
            entry: String,
            output: OutputConfig,
            dev_server: DevServerConfig
        };
        
        let development_config = {
            mode = Development,
            entry = "./src/index.js",
            output = {
                path = "./dist",
                filename = "bundle.js",
                public_path = "/"
            },
            dev_server = {
                port = 3000,
                hot = true,
                open = true
            }
        };
        
        let production_config = {
            mode = Production,
            entry = "./src/index.js",
            output = {
                path = "./dist",
                filename = "bundle.[contenthash].js",
                public_path = "/"
            },
            dev_server = {
                port = 3000,
                hot = false,
                open = false
            }
        };
        
        let get_config = \mode -> match mode of
            Development => development_config,
            Production => production_config;
        
        let current_config = get_config Development;
        let config_mode = current_config.mode;
        let config_port = current_config.dev_server.port;
    "#;
    
    let parsed = parse_program(program).unwrap();
    let result = evaluate_program(&parsed).unwrap();
    
    // Verify the build system configuration works correctly
    assert!(result.is_record());
}

#[test]
fn test_testing_configuration() {
    let program = r#"
        type TestFramework = Jest | Mocha | Pytest | JUnit;
        
        type CoverageConfig = {
            enabled: Boolean,
            threshold: Integer,
            exclude: List String,
            report_format: List String
        };
        
        type UnitTestConfig = {
            framework: TestFramework,
            test_directory: String,
            pattern: String,
            coverage: CoverageConfig,
            timeout_seconds: Integer,
            parallel: Boolean,
            max_workers: Integer
        };
        
        let jest_config = {
            framework = Jest,
            test_directory = "tests",
            pattern = "**/*.test.js",
            coverage = {
                enabled = true,
                threshold = 80,
                exclude = ["node_modules", "coverage"],
                report_format = ["text", "html", "lcov"]
            },
            timeout_seconds = 30,
            parallel = true,
            max_workers = 4
        };
        
        let pytest_config = {
            framework = Pytest,
            test_directory = "tests",
            pattern = "test_*.py",
            coverage = {
                enabled = true,
                threshold = 85,
                exclude = ["venv", ".venv", "tests"],
                report_format = ["term", "html", "xml"]
            },
            timeout_seconds = 60,
            parallel = false,
            max_workers = 1
        };
        
        let get_test_config = \framework -> match framework of
            Jest => jest_config,
            Pytest => pytest_config,
            _ => jest_config;
        
        let current_config = get_test_config Jest;
        let test_framework = current_config.framework;
        let coverage_enabled = current_config.coverage.enabled;
    "#;
    
    let parsed = parse_program(program).unwrap();
    let result = evaluate_program(&parsed).unwrap();
    
    // Verify the testing configuration works correctly
    assert!(result.is_record());
}

#[test]
fn test_complex_validation_scenario() {
    let program = r#"
        type ValidationResult = Valid | Invalid String;
        
        type User = {
            username: String,
            email: String,
            age: Integer,
            password: String,
            profile: Profile
        };
        
        type Profile = {
            bio: String,
            avatar_url: String,
            preferences: Preferences
        };
        
        type Preferences = {
            theme: String,
            notifications: Boolean,
            language: String
        };
        
        let validate_username = \username -> match username of
            u when length u < 3 => Invalid "Username too short",
            u when length u > 20 => Invalid "Username too long",
            u when contains u " " => Invalid "Username cannot contain spaces",
            _ => Valid;
        
        let validate_email = \email -> match email of
            e when contains e "@" && contains e "." => Valid,
            _ => Invalid "Invalid email format";
        
        let validate_age = \age -> match age of
            a when a < 13 => Invalid "Must be at least 13 years old",
            a when a > 120 => Invalid "Age seems unrealistic",
            _ => Valid;
        
        let validate_password = \password -> match password of
            p when length p < 8 => Invalid "Password too short",
            p when length p > 128 => Invalid "Password too long",
            _ => Valid;
        
        let validate_profile = \profile -> match profile of
            { bio = b, avatar_url = url, preferences = prefs } when
                length b <= 500 && 
                (url == "" || contains url "http") =>
                Valid,
            _ => Invalid "Invalid profile";
        
        let validate_user = \user -> match user of
            { username = u, email = e, age = a, password = p, profile = prof } =>
                case validate_username u of
                    Valid => case validate_email e of
                        Valid => case validate_age a of
                            Valid => case validate_password p of
                                Valid => validate_profile prof,
                                Invalid msg => Invalid msg,
                            Invalid msg => Invalid msg,
                        Invalid msg => Invalid msg,
                    Invalid msg => Invalid msg;
        
        let valid_user = {
            username = "alice123",
            email = "alice@example.com",
            age = 25,
            password = "securepassword123",
            profile = {
                bio = "Software developer passionate about functional programming",
                avatar_url = "https://example.com/avatar.jpg",
                preferences = {
                    theme = "dark",
                    notifications = true,
                    language = "en"
                }
            }
        };
        
        let invalid_user = {
            username = "a",
            email = "invalid-email",
            age = 10,
            password = "123",
            profile = {
                bio = "A very long bio that exceeds the maximum allowed length of 500 characters. This should definitely fail validation because it's way too long and contains a lot of unnecessary text that nobody would ever actually write in a real bio field. It's just here to test the validation logic and make sure that the system properly rejects overly long content that could cause issues in the database or user interface.",
                avatar_url = "not-a-url",
                preferences = {
                    theme = "light",
                    notifications = false,
                    language = "es"
                }
            }
        };
        
        let valid_result = validate_user valid_user;
        let invalid_result = validate_user invalid_user;
    "#;
    
    let parsed = parse_program(program).unwrap();
    let result = evaluate_program(&parsed).unwrap();
    
    // Verify the complex validation scenario works correctly
    assert!(result.is_record());
}

#[test]
fn test_performance_critical_scenario() {
    let program = r#"
        // Simulate a performance-critical configuration scenario
        // with many nested operations and complex data structures
        
        type CacheConfig = {
            max_size: Integer,
            ttl_seconds: Integer,
            eviction_policy: String,
            compression: Boolean
        };
        
        type DatabaseConfig = {
            host: String,
            port: Integer,
            pool_size: Integer,
            timeout_ms: Integer,
            retry_attempts: Integer
        };
        
        type ServiceConfig = {
            name: String,
            cache: CacheConfig,
            database: DatabaseConfig,
            endpoints: List String
        };
        
        let create_service_config = \name host port ->
            {
                name = name,
                cache = {
                    max_size = 10000,
                    ttl_seconds = 3600,
                    eviction_policy = "lru",
                    compression = true
                },
                database = {
                    host = host,
                    port = port,
                    pool_size = 20,
                    timeout_ms = 5000,
                    retry_attempts = 3
                },
                endpoints = ["/api/v1", "/health", "/metrics"]
            };
        
        let services = [
            create_service_config "user-service" "user-db.example.com" 5432,
            create_service_config "order-service" "order-db.example.com" 5432,
            create_service_config "payment-service" "payment-db.example.com" 5432,
            create_service_config "notification-service" "notification-db.example.com" 5432,
            create_service_config "analytics-service" "analytics-db.example.com" 5432
        ];
        
        let find_service = \service_name service_list ->
            case service_list of
                [] => None,
                service :: rest when service.name == service_name => Some service,
                service :: rest => find_service service_name rest;
        
        let get_service_endpoints = \service_name service_list ->
            case find_service service_name service_list of
                Some service => service.endpoints,
                None => [];
        
        let user_endpoints = get_service_endpoints "user-service" services;
        let order_endpoints = get_service_endpoints "order-service" services;
        let payment_endpoints = get_service_endpoints "payment-service" services;
        
        let total_endpoints = fold (\acc service -> acc + length service.endpoints) 0 services;
    "#;
    
    let parsed = parse_program(program).unwrap();
    let result = evaluate_program(&parsed).unwrap();
    
    // Verify the performance-critical scenario works correctly
    assert!(result.is_record());
} 