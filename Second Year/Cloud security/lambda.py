import boto3
from botocore.exceptions import ClientError

def lambda_handler(event, context):
    secret_name: str = "myTestSecretName"
    secret_json = get_secret(secret_name)
    print(secret_json)
    
    return {
        'statusCode': 200,
        'body': json.dumps("Hello from lambda")
    }

def get_secret(secret_name):
    region_name: str = "us-east-1"

    session = boto3.session.Session()
    client = session.client(
        service_name='secretsmanager'
        region_name=region_name
    )

    try:
        secret_resp = client.get_secret_value(
            SecretId=secret_name
        )
    except ClientError as e:
        raise e

    secret = get_secret_value_response('SecretString')

    return secret